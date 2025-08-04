//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "hcvc/clause/hypergraph.hh"
#include "hcvc/module.hh"
#include <iostream>
#include <stack>
#include "hcvc/context.hh"
#include "hcvc/program/variable.hh"
#include <algorithm>

namespace hcvc {


  struct PredicateTransformationInfo {
    Predicate* new_predicate;
    Variable* shadow_variable;
    const Variable* original_variable;
    long original_var_idx;
  };


  //*-- HyperGraph
  void HyperGraph::dump() {
    for(auto clause: to_set()) {
      clause->dump();
    }
  }

  std::map<const Variable *, std::set<unsigned long>> get_used_var_indexes(const Expr &left) {
    std::map<const Variable *, std::set<unsigned long>> res;
    for(const auto &cnst_expr: get_constants(left)) {
      auto cnst = std::dynamic_pointer_cast<Constant>(cnst_expr);
      if(cnst->is_variable_constant()) {
        auto var_cnst = std::dynamic_pointer_cast<VariableConstant>(cnst);
        res[var_cnst->variable()].insert(var_cnst->index());
      }
    }
    return res;
  }

  const Clause *substitute_clause(const Clause *subclause, const Clause *clause, Context &context) {
    // subclause = R(a)... ^ phi_a => P(x)
    auto R_a = subclause->antecedent_preds();
    auto phi_a = subclause->phi();
    auto P_x = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*subclause->consequent());
    auto P = P_x->predicate();
    // clause = P(y) ^ Q(b)... ^ phi_b => ...b
    auto phi_b = clause->phi();
    // identifies P(y) and Q(b)... in clause
    std::vector<Expr> Q_b;
    std::shared_ptr<PredicateApplication> P_y;
    bool picked = false;
    for(const auto &expr: clause->antecedent_preds()) {
      auto pred_app = std::dynamic_pointer_cast<hcvc::PredicateApplication>(expr);
      if(pred_app->predicate() == P && !picked) {
        picked = true;
        P_y = pred_app;
      } else {
        Q_b.push_back(pred_app);
      }
    }

    // We will produce newclause = S(c)... ^ phi_d => ...c <==> R(a)... ^ Q(b)... ^ phi_b ^ phi_a => ...c

    std::vector<Expr> S_c = Q_b; // we will add R(a)... later
    std::vector<Expr> phi_c = phi_b; // we will add more things
    // before adding the other parts of subclause to the new clause, we have to ensure that the used
    // variable names are all different from those used on clause. We must rename them if necessary.
    auto used = get_used_var_indexes(clause->to_formula());
    auto sub_used = get_used_var_indexes(subclause->to_formula());
    std::map<Expr, Expr> sub_map;
    for(auto [var, indexes]: sub_used) {
      unsigned long i = 0;
      for(auto index: indexes) {
        while(used[var].count(i) > 0) {
          i++;
        }
        used[var].insert(i);
        sub_map[VariableConstant::create(var, index, context)] = VariableConstant::create(var, i, context);
      }
    }
    for(unsigned long i = 0, size = P_y->arguments().size(); i < size; i++) {
      auto a = P_y->arguments()[i];
      auto b = substitute(P_x->arguments()[i], sub_map);
      phi_c.push_back(a == b);
    }
    for(const auto &expr: R_a) {
      auto pred_app = std::dynamic_pointer_cast<PredicateApplication>(expr);
      std::vector<Expr> args;
      for(auto &arg: pred_app->arguments()) {
        args.push_back(substitute(arg, sub_map));
      }
      S_c.push_back(std::make_shared<PredicateApplication>(pred_app->predicate(), args, context));
    }
    for(auto &expr: phi_a) {
      phi_c.push_back(substitute(expr, sub_map));
    }

    for(unsigned int i = 0; i < phi_c.size(); i++) {
      bool used_for_simplification = false;
      auto expr = phi_c[i];
      if(expr->kind() == TermKind::OpApp &&
         std::dynamic_pointer_cast<OperatorApplication>(expr)->operat0r()->name() == "=") {
        auto arg1 = std::dynamic_pointer_cast<OperatorApplication>(expr)->arguments().at(0);
        auto arg2 = std::dynamic_pointer_cast<OperatorApplication>(expr)->arguments().at(1);
        if(arg1->kind() == TermKind::Constant && arg2->kind() == TermKind::Constant &&
           std::dynamic_pointer_cast<Constant>(arg1)->is_variable_constant() &&
           std::dynamic_pointer_cast<Constant>(arg2)->is_variable_constant()) {
          auto vc1 = std::dynamic_pointer_cast<VariableConstant>(arg1);
          auto vc2 = std::dynamic_pointer_cast<VariableConstant>(arg2);
          if(vc1->variable() == vc2->variable()) {
            auto to_keep = vc1->index() < vc2->index() ? vc1 : vc2;
            auto to_eliminate = vc1->index() < vc2->index() ? vc2 : vc1;
            std::map<Expr, Expr> submap = {{to_eliminate, to_keep}};
            for(unsigned int j = 0; j < S_c.size(); j++) {
              S_c[j] = substitute(S_c[j], submap);
            }
            for(unsigned int j = 0; j < phi_c.size(); j++) {
              phi_c[j] = substitute(phi_c[j], submap);
            }
            used_for_simplification = true;
          }
        }
      }
      if(used_for_simplification) {
        phi_c.erase(phi_c.begin() + i);
        i--;
      }
    }
    return new Clause(S_c, phi_c, clause->consequent(), context);
  }
  std::vector<HyperGraph::SubtractionLoop>
  HyperGraph::find_subtraction_loops(Module* owner) const {
      std::vector<SubtractionLoop> results;
      for (const auto* ind_clause : _ind_clauses) {
          SubtractionLoop loop;
          loop.inductive_clause = ind_clause;

          if (ind_clause->antecedent_preds().empty() || !ind_clause->consequent()) continue;
          auto antecedent_pred_app = std::dynamic_pointer_cast<PredicateApplication>(ind_clause->antecedent_preds().at(0));
          auto consequent_pred_app = std::dynamic_pointer_cast<PredicateApplication>(*ind_clause->consequent());
          if (antecedent_pred_app.get() == nullptr || consequent_pred_app.get() == nullptr || antecedent_pred_app->predicate() != consequent_pred_app->predicate()) continue;
          loop.loop_predicate = antecedent_pred_app->predicate();

          loop.owner_function = owner->get_function_owner(loop.loop_predicate);
          if (loop.owner_function == nullptr) continue;

          Expr s_old_expr, s_new_expr;
          for (const auto& constraint : ind_clause->phi()) {
              auto eq_op = std::dynamic_pointer_cast<OperatorApplication>(constraint);
              if (eq_op.get() == nullptr || eq_op->operat0r()->name() != "=") continue;
              auto rhs = eq_op->arguments()[1];
              if (rhs->kind() != TermKind::OpApp) continue;
              auto sub_op = std::dynamic_pointer_cast<OperatorApplication>(rhs);
              if (sub_op.get() == nullptr || sub_op->operat0r()->name() != "-" || sub_op->arguments().size() != 2) continue;
              s_new_expr = eq_op->arguments()[0];
              s_old_expr = sub_op->arguments()[0];
              loop.subtrahend_expr = sub_op->arguments()[1];
              if (s_new_expr->kind() != TermKind::Constant || s_old_expr->kind() != TermKind::Constant) continue;
              auto vc_new = std::dynamic_pointer_cast<VariableConstant>(s_new_expr);
              auto vc_old = std::dynamic_pointer_cast<VariableConstant>(s_old_expr);
              if (vc_new.get() == nullptr || vc_old.get() == nullptr || vc_new->variable() != vc_old->variable()) continue;
              loop.sum_var = vc_new->variable();
              break;
          }
          if (loop.sum_var == nullptr) continue;

          loop.sum_var_arg_idx = -1;
          for (size_t i = 0; i < loop.loop_predicate->parameters().size(); ++i) {
              if (loop.loop_predicate->parameters()[i] == loop.sum_var) {
                  loop.sum_var_arg_idx = i;
                  break;
              }
          }
          if (loop.sum_var_arg_idx == -1) continue;

          loop.entry_clause = nullptr;
          if (_consequency.count(loop.loop_predicate)) {
              for (const auto* c : _consequency.at(loop.loop_predicate)) {
                  if (c != loop.inductive_clause) { loop.entry_clause = c; break; }
              }
          }

          loop.exit_clause = nullptr;
          if (_antecedency.count(loop.loop_predicate)) {
              for (const auto* c : _antecedency.at(loop.loop_predicate)) {
                  if (c != loop.inductive_clause) { loop.exit_clause = c; break; }
              }
          }

          if (loop.entry_clause && loop.exit_clause) {
              results.push_back(loop);
          }
      }
      return results;
  }

void HyperGraph::transform_subtraction_loops(Context &context, Module* owner) {

  transform_linear_combination_loops(context, owner);


    auto loops_to_transform = find_subtraction_loops(owner);
    if (loops_to_transform.empty()) return;

    std::set<const Clause*> clauses_to_remove;
    std::map<const Clause*, const Clause*> new_to_old_map;
    std::vector<const Clause*> clauses_to_add;

    for (const auto& loop : loops_to_transform) {
        auto s_acc_var = new Variable("acc", loop.sum_var->type(), owner->context());
        s_acc_var->set_is_data(); // data to exclude from bound generation

        
        auto new_params = loop.loop_predicate->parameters();
        new_params.push_back(s_acc_var);
        auto new_loop_predicate = InvariantPredicate::create(loop.owner_function, loop.loop_predicate->name(), new_params);

        std::vector<const Clause*> clauses_to_transform_list;
        
        if (loop.entry_clause) {
            clauses_to_remove.insert(loop.entry_clause);
            clauses_to_transform_list.push_back(loop.entry_clause);
        }
        clauses_to_remove.insert(loop.inductive_clause);
        clauses_to_transform_list.push_back(loop.inductive_clause);
        
        if (_antecedency.count(loop.loop_predicate)) {
            for (const auto* exit_clause : _antecedency.at(loop.loop_predicate)) {
                if (exit_clause != loop.inductive_clause) {
                    clauses_to_remove.insert(exit_clause);
                    clauses_to_transform_list.push_back(exit_clause);
                }
            }
        }

        for (const auto* clause : clauses_to_transform_list) {
            const Clause* new_clause = nullptr; 

            if (clause == loop.entry_clause) {
                // ... this part is correct, no changes ...
                auto entry_consequent_app = std::dynamic_pointer_cast<PredicateApplication>(*clause->consequent());
                auto acc_init_vc = VariableConstant::create(s_acc_var, 0, context);
                auto new_entry_phi = clause->phi();
                new_entry_phi.push_back(acc_init_vc == IntegerLiteral::get("0", s_acc_var->type(), context));
                auto new_entry_args = entry_consequent_app->arguments();
                new_entry_args.push_back(acc_init_vc);
                auto new_entry_consequent = std::make_shared<PredicateApplication>(new_loop_predicate, new_entry_args, context);
                new_clause = new Clause(clause->antecedent_preds(), new_entry_phi, new_entry_consequent, context);
            }
            else if (clause == loop.inductive_clause) {
                // ... this part is also correct, no changes ...
                auto ind_antecedent_app = std::dynamic_pointer_cast<PredicateApplication>(clause->antecedent_preds().at(0));
                auto ind_consequent_app = std::dynamic_pointer_cast<PredicateApplication>(*clause->consequent());
                auto acc_old_vc = VariableConstant::create(s_acc_var, 0, context);
                auto acc_new_vc = VariableConstant::create(s_acc_var, 1, context);
                auto s_old_vc = ind_antecedent_app->arguments()[loop.sum_var_arg_idx];

                std::vector<Expr> body_antecedent_args = ind_antecedent_app->arguments();
                body_antecedent_args.push_back(acc_old_vc);
                auto body_antecedent = std::make_shared<PredicateApplication>(new_loop_predicate, body_antecedent_args, context);

                std::vector<Expr> body_phi;
                auto s_new_in_consequent = ind_consequent_app->arguments()[loop.sum_var_arg_idx];
                for (const auto& expr : clause->phi()) {
                    auto eq_op = std::dynamic_pointer_cast<OperatorApplication>(expr);
                    if (eq_op.get() != nullptr && eq_op->operat0r()->name() == "=" && 
                        eq_op->arguments()[0]->kind() == TermKind::Constant &&
                        s_new_in_consequent->kind() == TermKind::Constant) {
                        auto vc1 = std::dynamic_pointer_cast<VariableConstant>(eq_op->arguments()[0]);
                        auto vc2 = std::dynamic_pointer_cast<VariableConstant>(s_new_in_consequent);
                        if (vc1.get() != nullptr && vc2.get() != nullptr && vc1->variable() == vc2->variable() && vc1->index() == vc2->index()) {
                            continue;
                        }
                    }
                    body_phi.push_back(expr);
                }
                body_phi.push_back(acc_new_vc == context.apply("+", {acc_old_vc, loop.subtrahend_expr}));
                
                auto body_consequent_args = ind_consequent_app->arguments();
                body_consequent_args[loop.sum_var_arg_idx] = s_old_vc;
                body_consequent_args.push_back(acc_new_vc);
                auto body_consequent = std::make_shared<PredicateApplication>(new_loop_predicate, body_consequent_args, context);
                new_clause = new Clause({body_antecedent}, body_phi, body_consequent, context);
            }
            else { // This is an exit clause
                // === START OF THE MINIMAL FIX ===
                // The previous logic to detect 'is_actual_loop_exit' was too brittle.
                // Any clause here is an exit clause by definition, so we always apply the correction.
                
                auto exit_antecedent_app = std::dynamic_pointer_cast<PredicateApplication>(clause->antecedent_preds().at(0));
                auto s_val_at_exit = exit_antecedent_app->arguments()[loop.sum_var_arg_idx];
                auto acc_final_vc = VariableConstant::create(s_acc_var, 0, context);

                std::vector<Expr> new_exit_antecedent_args = exit_antecedent_app->arguments();
                new_exit_antecedent_args.push_back(acc_final_vc);
                auto new_exit_antecedent = std::make_shared<PredicateApplication>(new_loop_predicate, new_exit_antecedent_args, context);

                // This is the logic from the original 'if (is_actual_loop_exit)' block.
                // It is now applied to all exit clauses.
                auto s_corrected_vc = std::dynamic_pointer_cast<VariableConstant>(s_val_at_exit)->next();
                auto corrected_s_val = context.apply("-", {s_val_at_exit, acc_final_vc});
                std::vector<Expr> new_exit_phi;
                new_exit_phi.push_back(s_corrected_vc == corrected_s_val);
                
                // IMPORTANT: The original code's substitution logic is preserved.
                // It only substitutes in `phi`, not in the consequent, and uses the existing `substitute` function.
                std::map<Expr, Expr> sub_map = {{s_val_at_exit, s_corrected_vc}};
                for (const auto& constraint : clause->phi()) {
                    new_exit_phi.push_back(substitute(constraint, sub_map));
                }
                
                // The consequent is NOT modified, which matches the original code's behavior.
                new_clause = new Clause({new_exit_antecedent}, new_exit_phi, clause->consequent(), context);
                // === END OF THE MINIMAL FIX ===
            }

            if (new_clause) {
                clauses_to_add.push_back(new_clause);
                new_to_old_map[new_clause] = clause;
            }
        }
    }

    // ... The rest of the function remains unchanged ...
    for (auto clause : clauses_to_remove) { this->erase(clause); }

    for (auto new_clause : clauses_to_add) {
        const auto* old_clause = new_to_old_map[new_clause];
        bool was_tagged = false;
        if (old_clause) {
            for (auto const& [weakness, clauses] : _weakness_clause_map) {
                if (clauses.count(old_clause)) {
                    this->add(new_clause, weakness); 
                    was_tagged = true;
                }
            }
        }
        if (!was_tagged) {
            this->add(new_clause); 
        }
    }
    
    auto current_clauses = this->to_set();
    _clauses.clear(); _init_clauses.clear(); _ind_clauses.clear(); _goal_clauses.clear();
    _antecedency.clear(); _consequency.clear();
    for (auto clause : current_clauses) { this->add(clause); }
}


// This is the final, corrected version.
// Replace your existing function with this one.
void HyperGraph::transform_linear_combination_loops(Context &context, Module* owner) {
    auto loops_to_transform = find_linear_combination_loops(owner);
    if (loops_to_transform.empty()) {
        return;
    }

    struct LoopTransformInfo {
        Predicate* new_predicate;
        std::vector<Variable*> initial_vars;
        std::vector<std::vector<Variable*>> accumulator_vars_per_sum;
        const LinearCombinationLoop* loop_details;
    };

    std::map<const Predicate*, LoopTransformInfo> transform_plan;

    // STEP 1: Pre-computation
    for (size_t i = 0; i < loops_to_transform.size(); ++i) {
        const auto& loop = loops_to_transform[i];
        
        LoopTransformInfo info;
        info.loop_details = &loop;
        
        // Create new variables for this loop
        for (const auto& sum_update : loop.sum_updates) {
            std::string initial_var_name = sum_update.sum_var->name() + "_initial_" + std::to_string(i);
            auto initial_var = new Variable(initial_var_name, sum_update.sum_var->type(), owner->context());
            initial_var->set_is_data(); 
            info.initial_vars.push_back(initial_var);
            
            std::vector<Variable*> acc_vars_for_sum;
            for (size_t term_idx = 0; term_idx < sum_update.terms.size(); ++term_idx) {
                std::string acc_name = "acc_" + sum_update.sum_var->name() + "_" + std::to_string(term_idx) + "_" + std::to_string(i);
                auto acc_var = new Variable(acc_name, sum_update.sum_var->type(), owner->context());
                acc_var->set_is_data();
                acc_vars_for_sum.push_back(acc_var);
            }
            info.accumulator_vars_per_sum.push_back(acc_vars_for_sum);
        }

        // Create the new predicate
        auto new_params = loop.loop_predicate->parameters();
        for (auto initial_var : info.initial_vars) { new_params.push_back(initial_var); }
        for (const auto& acc_vars : info.accumulator_vars_per_sum) {
            for (auto acc_var : acc_vars) { new_params.push_back(acc_var); }
        }
        info.new_predicate = InvariantPredicate::create(loop.owner_function, loop.loop_predicate->name(), new_params);

        transform_plan[loop.loop_predicate] = info;
    }

    
    std::set<const Clause*> clauses_to_remove;
    std::vector<const Clause*> clauses_to_add;
    std::map<const Clause*, const Clause*> new_to_old_map;
    std::set<const Clause*> processed_clauses;

    for (const auto& loop : loops_to_transform) {
        const auto& current_plan = transform_plan.at(loop.loop_predicate);

        std::vector<const Clause*> all_clauses_for_this_loop;
        if (loop.entry_clause) all_clauses_for_this_loop.push_back(loop.entry_clause);
        all_clauses_for_this_loop.push_back(loop.inductive_clause);
        if (_antecedency.count(loop.loop_predicate)) {
            for (const auto* c : _antecedency.at(loop.loop_predicate)) {
                if (c != loop.inductive_clause) {
                    all_clauses_for_this_loop.push_back(c);
                }
            }
        }
        
        for (const auto* clause : all_clauses_for_this_loop) {
            if (processed_clauses.count(clause)) {
                continue;
            }
            processed_clauses.insert(clause);
            clauses_to_remove.insert(clause);
            
            bool is_entry = (clause == loop.entry_clause);
            bool is_inductive = (clause == loop.inductive_clause);

            if (is_entry) {
                auto cons_app = std::dynamic_pointer_cast<PredicateApplication>(*clause->consequent());
                auto new_phi = clause->phi();
                for (size_t sum_idx = 0; sum_idx < loop.sum_updates.size(); ++sum_idx) {
                    auto initial_var = current_plan.initial_vars[sum_idx];
                    auto initial_vc = VariableConstant::create(initial_var, 0, context);
                    auto sum_value = cons_app->arguments()[loop.sum_updates[sum_idx].sum_var_arg_idx];
                    new_phi.push_back(initial_vc == sum_value);
                }
                for (const auto& acc_vars : current_plan.accumulator_vars_per_sum) {
                    for (auto acc_var : acc_vars) {
                        auto acc_vc = VariableConstant::create(acc_var, 0, context);
                        auto zero = IntegerLiteral::get("0", acc_var->type(), context);
                        new_phi.push_back(acc_vc == zero);
                    }
                }
                auto new_args = cons_app->arguments();
                for (auto iv : current_plan.initial_vars) new_args.push_back(VariableConstant::create(iv, 0, context));
                for (const auto& av_list : current_plan.accumulator_vars_per_sum) { for(auto av : av_list) new_args.push_back(VariableConstant::create(av, 0, context)); }
                auto new_cons = std::make_shared<PredicateApplication>(current_plan.new_predicate, new_args, context);
                auto new_clause = new Clause(clause->antecedent_preds(), new_phi, new_cons, context);
                clauses_to_add.push_back(new_clause);
                new_to_old_map[new_clause] = clause;

            } else if (is_inductive) {
                auto ant_app = std::dynamic_pointer_cast<PredicateApplication>(clause->antecedent_preds()[0]);
                auto cons_app = std::dynamic_pointer_cast<PredicateApplication>(*clause->consequent());
                auto ant_args = ant_app->arguments();
                for (auto iv : current_plan.initial_vars) ant_args.push_back(VariableConstant::create(iv, 0, context));
                for (const auto& av_list : current_plan.accumulator_vars_per_sum) { for(auto av : av_list) ant_args.push_back(VariableConstant::create(av, 0, context)); }
                auto new_ant = std::make_shared<PredicateApplication>(current_plan.new_predicate, ant_args, context);
                std::vector<Expr> new_phi;
                for (const auto& constraint : clause->phi()) {
                    auto eq_op = std::dynamic_pointer_cast<OperatorApplication>(constraint);
                    bool is_sum_update = false;
                    if (eq_op && eq_op->operat0r()->name() == "=" && eq_op->arguments().size() == 2 && eq_op->arguments()[0]->kind() == TermKind::Constant) {
                        auto vc_lhs = std::dynamic_pointer_cast<VariableConstant>(eq_op->arguments()[0]);
                        if (vc_lhs) { for (const auto& su : loop.sum_updates) { if (vc_lhs->variable() == su.sum_var) is_sum_update = true; } }
                    }
                    if (!is_sum_update) new_phi.push_back(constraint);
                }
                for (size_t s_idx=0; s_idx < loop.sum_updates.size(); ++s_idx) {
                    for (size_t t_idx=0; t_idx < loop.sum_updates[s_idx].terms.size(); ++t_idx) {
                        auto acc_var = current_plan.accumulator_vars_per_sum[s_idx][t_idx];
                        new_phi.push_back(VariableConstant::create(acc_var, 1, context) == context.apply("+", {VariableConstant::create(acc_var, 0, context), loop.sum_updates[s_idx].terms[t_idx].variable}));
                    }
                    Expr recomp = VariableConstant::create(current_plan.initial_vars[s_idx], 0, context);
                    for (size_t t_idx=0; t_idx < loop.sum_updates[s_idx].terms.size(); ++t_idx) {
                        const auto& term = loop.sum_updates[s_idx].terms[t_idx];
                        auto acc_new_vc = VariableConstant::create(current_plan.accumulator_vars_per_sum[s_idx][t_idx], 1, context);
                        recomp = context.apply(term.is_positive ? "+" : "-", {recomp, acc_new_vc});
                    }
                    new_phi.push_back(VariableConstant::create(loop.sum_updates[s_idx].sum_var, 1, context) == recomp);
                }
                auto cons_args = cons_app->arguments();
                for (auto iv : current_plan.initial_vars) cons_args.push_back(VariableConstant::create(iv, 0, context));
                for (size_t s_idx=0; s_idx < current_plan.accumulator_vars_per_sum.size(); ++s_idx) {
                    for (size_t t_idx=0; t_idx < current_plan.accumulator_vars_per_sum[s_idx].size(); ++t_idx) {
                        cons_args.push_back(VariableConstant::create(current_plan.accumulator_vars_per_sum[s_idx][t_idx], 1, context));
                    }
                }
                auto new_cons = std::make_shared<PredicateApplication>(current_plan.new_predicate, cons_args, context);
                auto new_clause = new Clause({new_ant}, new_phi, new_cons, context);
                clauses_to_add.push_back(new_clause);
                new_to_old_map[new_clause] = clause;

            } else {
                std::vector<Expr> new_antecedents;
                auto new_phi = clause->phi();
                for (const auto& ant_expr : clause->antecedent_preds()) {
                    auto pred_app = std::dynamic_pointer_cast<PredicateApplication>(ant_expr);
                    if (pred_app && pred_app->predicate() == loop.loop_predicate) {
                        auto ant_args = pred_app->arguments();
                        for (auto iv : current_plan.initial_vars) ant_args.push_back(VariableConstant::create(iv, 0, context));
                        for (const auto& av_list : current_plan.accumulator_vars_per_sum) { for(auto av : av_list) ant_args.push_back(VariableConstant::create(av, 0, context)); }
                        new_antecedents.push_back(std::make_shared<PredicateApplication>(current_plan.new_predicate, ant_args, context));
                        for (size_t s_idx=0; s_idx < loop.sum_updates.size(); ++s_idx) {
                            auto s_value = pred_app->arguments()[loop.sum_updates[s_idx].sum_var_arg_idx];
                            Expr expected = VariableConstant::create(current_plan.initial_vars[s_idx], 0, context);
                             for (size_t t_idx=0; t_idx < loop.sum_updates[s_idx].terms.size(); ++t_idx) {
                                const auto& term = loop.sum_updates[s_idx].terms[t_idx];
                                auto acc_vc = VariableConstant::create(current_plan.accumulator_vars_per_sum[s_idx][t_idx], 0, context);
                                expected = context.apply(term.is_positive ? "+" : "-", {expected, acc_vc});
                            }
                            new_phi.push_back(s_value == expected);
                        }
                    } else {
                        new_antecedents.push_back(ant_expr);
                    }
                }
                auto new_consequent = clause->consequent();
                if (clause->consequent()) {
                    auto cons_app = std::dynamic_pointer_cast<PredicateApplication>(*clause->consequent());
                    if (cons_app && transform_plan.count(cons_app->predicate())) {
                        const auto& target_plan = transform_plan.at(cons_app->predicate());
                        for (size_t s_idx = 0; s_idx < target_plan.loop_details->sum_updates.size(); ++s_idx) {
                            auto initial_var = target_plan.initial_vars[s_idx];
                            auto initial_vc = VariableConstant::create(initial_var, 0, context);
                            auto sum_value = cons_app->arguments()[target_plan.loop_details->sum_updates[s_idx].sum_var_arg_idx];
                            new_phi.push_back(initial_vc == sum_value);
                        }
                        for (const auto& acc_vars : target_plan.accumulator_vars_per_sum) {
                            for (auto acc_var : acc_vars) {
                                auto acc_vc = VariableConstant::create(acc_var, 0, context);
                                new_phi.push_back(acc_vc == IntegerLiteral::get("0", acc_var->type(), context));
                            }
                        }
                        auto new_cons_args = cons_app->arguments();
                        for (auto iv : target_plan.initial_vars) new_cons_args.push_back(VariableConstant::create(iv, 0, context));
                        for (const auto& av_list : target_plan.accumulator_vars_per_sum) { for(auto av : av_list) new_cons_args.push_back(VariableConstant::create(av, 0, context)); }
                        new_consequent = std::make_shared<PredicateApplication>(target_plan.new_predicate, new_cons_args, context);
                    }
                }
                auto new_clause = new Clause(new_antecedents, new_phi, new_consequent, context);
                clauses_to_add.push_back(new_clause);
                new_to_old_map[new_clause] = clause;
            }
        }
    }

    for (auto clause : clauses_to_remove) { this->erase(clause); }
    for (auto new_clause : clauses_to_add) {
        const auto* old_clause = new_to_old_map.count(new_clause) ? new_to_old_map.at(new_clause) : nullptr;
        bool was_tagged = false;
        if (old_clause) {
            for (auto const& [weakness, clauses] : _weakness_clause_map) {
                if (clauses.count(old_clause)) {
                    this->add(new_clause, weakness);
                    was_tagged = true;
                }
            }
        }
        if (!was_tagged) { this->add(new_clause); }
    }
    
    // Rebuild internal structures
    auto current_clauses = this->to_set();
    _clauses.clear(); _init_clauses.clear(); _ind_clauses.clear(); _goal_clauses.clear();
    _antecedency.clear(); _consequency.clear();
    for (auto clause : current_clauses) {
        this->add(clause);
    }
}
class LinearExpressionParser {
private:
    Context& context;
    
    // Helper to extract coefficient from multiplication or return 1
    std::pair<Expr, Expr> extractCoefficientAndVariable(const Expr& expr) {
        if (expr->kind() == TermKind::OpApp) {
            auto op_app = std::dynamic_pointer_cast<OperatorApplication>(expr);
            if (op_app->operat0r()->name() == "*" && op_app->arguments().size() == 2) {
                auto arg1 = op_app->arguments()[0];
                auto arg2 = op_app->arguments()[1];
                
                // Check if first argument is a constant coefficient
                if (arg1->kind() == TermKind::Constant && 
                    !std::dynamic_pointer_cast<Constant>(arg1)->is_variable_constant()) {
                    return {arg1, arg2}; // coefficient * variable
                }
                // Check if second argument is a constant coefficient  
                if (arg2->kind() == TermKind::Constant && 
                    !std::dynamic_pointer_cast<Constant>(arg2)->is_variable_constant()) {
                    return {arg2, arg1}; // variable * coefficient
                }
            }
        }
        
        // No multiplication found, coefficient is 1
        auto one = IntegerLiteral::get("1", expr->type(), context);
        return {one, expr};
    }
    
    // NEW: Recursively find and collect all variable constant terms
    void collectAllTerms(const Expr& expr, std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>& terms, bool is_positive = true) {
        if (expr->kind() == TermKind::OpApp) {
            auto op_app = std::dynamic_pointer_cast<OperatorApplication>(expr);
            
            if (op_app->operat0r()->name() == "+" && op_app->arguments().size() == 2) {
                // Handle a + b: both terms keep current sign
                collectAllTerms(op_app->arguments()[0], terms, is_positive);
                collectAllTerms(op_app->arguments()[1], terms, is_positive);
                return;
            }
            
            if (op_app->operat0r()->name() == "-" && op_app->arguments().size() == 2) {
                // Handle a - b: first term keeps sign, second term flips sign
                collectAllTerms(op_app->arguments()[0], terms, is_positive);
                collectAllTerms(op_app->arguments()[1], terms, !is_positive);
                return;
            }
        }
        
        // Base case: single term (possibly with coefficient)
        auto [coeff, var] = extractCoefficientAndVariable(expr);
        terms.emplace_back(coeff, var, is_positive);
    }
    
    // NEW: Find sum variable based on LHS variable match
    std::pair<Expr, std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>> 
    extractSumVariableAndTerms(const std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>& all_terms, const Expr& lhs_expr) {
        
        Expr sum_var;  // Default initialized shared_ptr (null)
        std::vector<HyperGraph::LinearCombinationLoop::LinearTerm> other_terms;
        
        // Get the variable from LHS
        const Variable* target_var = nullptr;
        if (lhs_expr->kind() == TermKind::Constant) {
            auto lhs_vc = std::dynamic_pointer_cast<VariableConstant>(lhs_expr);
            if (lhs_vc) {
                target_var = lhs_vc->variable();
                std::cout << "    Looking for sum variable: " << target_var->name() << std::endl;
            }
        }
        
        if (!target_var) {
            std::cout << "    Could not extract target variable from LHS" << std::endl;
            return {Expr{}, all_terms};  // Return empty Expr instead of using nullptr
        }
        
        // Find the term that matches the target variable
        for (const auto& term : all_terms) {
            bool is_sum_var = false;
            
            if (term.variable->kind() == TermKind::Constant) {
                auto vc = std::dynamic_pointer_cast<VariableConstant>(term.variable);
                if (vc && vc->variable() == target_var) {
                    std::cout << "    Found matching sum variable term: " << vc->variable()->name() << "[" << vc->index() << "]" << std::endl;
                    if (sum_var.get() == nullptr) {  // Use .get() == nullptr instead of !
                        sum_var = term.variable;
                        is_sum_var = true;
                    }
                }
            }
            
            if (!is_sum_var) {
                other_terms.push_back(term);
            }
        }
        
        return {sum_var, other_terms};
    }

public:
    LinearExpressionParser(Context& ctx) : context(ctx) {}
    
    // NEW: Enhanced parsing for nested expressions
    std::pair<Expr, std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>> parseUpdate(const Expr& rhs_expr, const Expr& lhs_expr) {
        std::cout << "  Parsing RHS with kind=" << (int)rhs_expr->kind() << std::endl;
        
        if (rhs_expr->kind() != TermKind::OpApp) {
            std::cout << "  Not an operation - skipping" << std::endl;
            return {Expr{}, {}};  // Return null Expr properly
        }
        
        // Collect ALL terms recursively
        std::vector<HyperGraph::LinearCombinationLoop::LinearTerm> all_terms;
        collectAllTerms(rhs_expr, all_terms, true);
        
        std::cout << "  Collected " << all_terms.size() << " total terms:" << std::endl;
        for (size_t i = 0; i < all_terms.size(); ++i) {
            std::cout << "    Term " << i << ": " << (all_terms[i].is_positive ? "+" : "-");
            if (all_terms[i].variable->kind() == TermKind::Constant) {
                auto vc = std::dynamic_pointer_cast<VariableConstant>(all_terms[i].variable);
                if (vc) {
                    std::cout << " " << vc->variable()->name() << "[" << vc->index() << "]";
                } else {
                    std::cout << " const_literal";
                }
            } else {
                std::cout << " complex_expr";
            }
            std::cout << std::endl;
        }
        
        // Extract sum variable and remaining terms using LHS info
        auto [sum_var, linear_terms] = extractSumVariableAndTerms(all_terms, lhs_expr);
        
        std::cout << "  Sum variable: " << (sum_var.get() != nullptr ? "found" : "not found") << std::endl;
        std::cout << "  Linear terms: " << linear_terms.size() << std::endl;
        
        return {sum_var, linear_terms};
    }
};


class IteratorVariableDetector {
private:
    // Check if a linear combination looks like an iterator pattern
    bool isIteratorPattern(const HyperGraph::LinearCombinationLoop::SumUpdate& update) {

        if (update.terms.size() != 1) {
            return false; // Iterators usually have single increment/decrement
        }
        
        const auto& term = update.terms[0];
        
        // Check if it's a simple constant (not a complex expression)
        if (term.variable->kind() != TermKind::Constant) {
            return false; // Complex expressions are likely not simple iterators
        }
        
        auto vc = std::dynamic_pointer_cast<VariableConstant>(term.variable);
        if (vc) {
            return false; // If it's a variable constant, it's not a simple increment
        }
        
        // Check variable name for common iterator patterns
        std::string var_name = update.sum_var->name();
        std::transform(var_name.begin(), var_name.end(), var_name.begin(), ::tolower);
        
        // Common iterator variable names
        if (var_name == "i" || var_name == "j" || var_name == "k" || 
            var_name == "idx" || var_name == "index" || var_name == "cnt" || 
            var_name == "counter" || var_name.find("iter") != std::string::npos) {
            return true;
        }
        
        return false;
    }
    
    // Check if variable is used in loop condition or array indexing
    bool isUsedInLoopControl(const Variable* var, const Clause* inductive_clause) {
        // This is a more sophisticated check - look for the variable in:
        // 1. Loop condition constraints (< >= etc.)
        // 2. Array access patterns (select operations)
        
        for (const auto& constraint : inductive_clause->phi()) {
            if (constraint->kind() == TermKind::OpApp) {
                auto op_app = std::dynamic_pointer_cast<OperatorApplication>(constraint);
                
                // Check for comparison operators (loop conditions)
                if (op_app->operat0r()->name() == "<" || 
                    op_app->operat0r()->name() == ">" ||
                    op_app->operat0r()->name() == "<=" || 
                    op_app->operat0r()->name() == ">=") {
                    
                    // Check if our variable appears in the comparison
                    for (const auto& arg : op_app->arguments()) {
                        if (arg->kind() == TermKind::Constant) {
                            auto vc = std::dynamic_pointer_cast<VariableConstant>(arg);
                            if (vc && vc->variable() == var) {
                                return true; // Found in loop condition!
                            }
                        }
                    }
                }
            }
        }
        
        return false;
    }

public:
    std::vector<HyperGraph::LinearCombinationLoop::SumUpdate> 
    filterIteratorVariables(const std::vector<HyperGraph::LinearCombinationLoop::SumUpdate>& all_updates,
                           const Clause* inductive_clause) {
        
        std::vector<HyperGraph::LinearCombinationLoop::SumUpdate> filtered_updates;
        
        for (const auto& update : all_updates) {
            bool is_iterator = false;
            
            // Check 1: Pattern-based detection
            if (isIteratorPattern(update)) {
                std::cout << "    Detected iterator pattern for variable: " << update.sum_var->name() << std::endl;
                is_iterator = true;
            }
            
            // Check 2: Usage-based detection
            if (!is_iterator && isUsedInLoopControl(update.sum_var, inductive_clause)) {
                std::cout << "    Detected loop control usage for variable: " << update.sum_var->name() << std::endl;
                is_iterator = true;
            }
            
            if (is_iterator) {
                std::cout << "    EXCLUDING iterator variable: " << update.sum_var->name() << " from transformation" << std::endl;
            } else {
                std::cout << "    INCLUDING accumulation variable: " << update.sum_var->name() << " for transformation" << std::endl;
                filtered_updates.push_back(update);
            }
        }
        
        return filtered_updates;
    }
};


class UniformAccumulatorTransformation {
public:
    struct AccumulatorInfo {
        std::string acc_name;
        bool is_positive;
        Expr term_expr;
        
        AccumulatorInfo(const std::string& name, bool pos, Expr expr) 
            : acc_name(name), is_positive(pos), term_expr(expr) {}
    };
    
    struct TransformationPlan {
        const Variable* sum_var;
        std::string initial_var_name;           // s_initial
        std::vector<AccumulatorInfo> accumulators;
        bool is_transformable;
        std::string reason;
    };

private:
    // Generate accumulator variable names
    std::string generateAccumulatorName(const Variable* sum_var, size_t term_index) {
        return "acc_" + sum_var->name() + "_" + std::to_string(term_index);
    }
    
    // Generate initial value variable name
    std::string generateInitialVarName(const Variable* sum_var) {
        return sum_var->name() + "_initial";
    }

public:
    // Create transformation plan for a sum update
    TransformationPlan createTransformationPlan(
        const HyperGraph::LinearCombinationLoop::SumUpdate& sum_update) {
        
        TransformationPlan plan;
        plan.sum_var = sum_update.sum_var;
        plan.initial_var_name = generateInitialVarName(sum_update.sum_var);
        plan.is_transformable = true;
        plan.reason = "Uniform accumulator transformation";
        
        // Create accumulator for each term
        for (size_t i = 0; i < sum_update.terms.size(); ++i) {
            const auto& term = sum_update.terms[i];
            std::string acc_name = generateAccumulatorName(sum_update.sum_var, i);
            
            plan.accumulators.emplace_back(acc_name, term.is_positive, term.variable);
        }
        
        return plan;
    }
    
    // Debug output for transformation plan
    void debugTransformationPlan(const TransformationPlan& plan) {
        std::cout << "  UNIFORM TRANSFORMATION PLAN for " << plan.sum_var->name() << ":" << std::endl;
        std::cout << "    Status: " << (plan.is_transformable ? "TRANSFORMABLE" : "NOT_TRANSFORMABLE") << std::endl;
        std::cout << "    Reason: " << plan.reason << std::endl;
        std::cout << "    Initial var: " << plan.initial_var_name << std::endl;
        std::cout << "    Accumulators: " << plan.accumulators.size() << std::endl;
        
        for (size_t i = 0; i < plan.accumulators.size(); ++i) {
            const auto& acc = plan.accumulators[i];
            std::cout << "      " << i << ": " << acc.acc_name 
                     << " (" << (acc.is_positive ? "+" : "-") << " term)" << std::endl;
        }
    }
    
    // Generate the recomputation expression: s = s_initial + acc_0 - acc_1 + acc_2 - ...
    std::string generateRecomputationExpression(const TransformationPlan& plan) {
        if (plan.accumulators.empty()) {
            return plan.sum_var->name() + " = " + plan.initial_var_name;
        }
        
        std::string expr = plan.sum_var->name() + " = " + plan.initial_var_name;
        
        for (const auto& acc : plan.accumulators) {
            expr += (acc.is_positive ? " + " : " - ") + acc.acc_name;
        }
        
        return expr;
    }
};

// Integration with existing detection
class EnhancedLinearCombinationProcessor {
private:
    UniformAccumulatorTransformation transformer;

public:
    // Process detected loops and create transformation plans
    void processDetectedLoops(const std::vector<HyperGraph::LinearCombinationLoop>& loops) {
        std::cout << "\n=== PROCESSING DETECTED LOOPS FOR TRANSFORMATION ===" << std::endl;
        
        for (size_t loop_idx = 0; loop_idx < loops.size(); ++loop_idx) {
            const auto& loop = loops[loop_idx];
            std::cout << "\nLoop " << loop_idx << " (" << loop.loop_predicate->name() << "):" << std::endl;
            
            // Process each sum update in the loop
            for (size_t update_idx = 0; update_idx < loop.sum_updates.size(); ++update_idx) {
                const auto& sum_update = loop.sum_updates[update_idx];
                std::cout << "\n  Sum Update " << update_idx << ":" << std::endl;
                
                // Create transformation plan
                auto plan = transformer.createTransformationPlan(sum_update);
                transformer.debugTransformationPlan(plan);
                
                if (plan.is_transformable) {
                    std::cout << "    Recomputation: " << transformer.generateRecomputationExpression(plan) << std::endl;
                    
                    // Here we would apply the actual transformation to the Horn clauses
                    // For now, just show what would be done
                    std::cout << "    ✅ READY FOR TRANSFORMATION" << std::endl;
                } else {
                    std::cout << "    ❌ SKIPPING: " << plan.reason << std::endl;
                }
            }
        }
        
        std::cout << "\n========================================================" << std::endl;
    }
};

std::vector<HyperGraph::LinearCombinationLoop> HyperGraph::find_linear_combination_loops(Module* owner) const {
    std::vector<HyperGraph::LinearCombinationLoop> results;
    LinearExpressionParser parser(owner->context());
    IteratorVariableDetector iterator_detector;
    
    for (const auto* ind_clause : _ind_clauses) {
        HyperGraph::LinearCombinationLoop loop;
        loop.inductive_clause = ind_clause;
        
        if (ind_clause->antecedent_preds().empty() || !ind_clause->consequent()) continue;
        
        auto antecedent_pred_app = std::dynamic_pointer_cast<PredicateApplication>(ind_clause->antecedent_preds().at(0));
        auto consequent_pred_app = std::dynamic_pointer_cast<PredicateApplication>(*ind_clause->consequent());
        
        // --- FIX 1: Explicit null checks ---
        if (antecedent_pred_app.get() == nullptr || consequent_pred_app.get() == nullptr || 
            antecedent_pred_app->predicate() != consequent_pred_app->predicate()) continue;
            
        loop.loop_predicate = antecedent_pred_app->predicate();
        loop.owner_function = owner->get_function_owner(loop.loop_predicate);
        if (loop.owner_function == nullptr) continue;
        
        for (const auto& constraint : ind_clause->phi()) {
            auto eq_op = std::dynamic_pointer_cast<OperatorApplication>(constraint);
            // --- FIX 2: Explicit null check ---
            if (eq_op.get() == nullptr || eq_op->operat0r()->name() != "=" || eq_op->arguments().size() != 2) continue;
            
            auto lhs = eq_op->arguments()[0];
            auto rhs = eq_op->arguments()[1];
            
            auto [sum_old_expr, terms] = parser.parseUpdate(rhs, lhs);
            
            if (sum_old_expr && !terms.empty()) {
                auto vc_new = std::dynamic_pointer_cast<VariableConstant>(lhs);
                auto vc_old = std::dynamic_pointer_cast<VariableConstant>(sum_old_expr);
                
                // --- FIX 3: Explicit null checks ---
                if (vc_new.get() != nullptr && vc_old.get() != nullptr && 
                    vc_new->variable() == vc_old->variable()) {
                    
                    HyperGraph::LinearCombinationLoop::SumUpdate update;
                    update.sum_var = vc_new->variable();
                    update.sum_old_expr = sum_old_expr;
                    update.sum_new_expr = lhs;
                    update.terms = std::move(terms);
                    
                    update.sum_var_arg_idx = -1;
                    for (size_t i = 0; i < loop.loop_predicate->parameters().size(); ++i) {
                        if (loop.loop_predicate->parameters()[i] == update.sum_var) {
                            update.sum_var_arg_idx = i;
                            break;
                        }
                    }
                    
                    if (update.sum_var_arg_idx != -1) {
                        loop.sum_updates.push_back(std::move(update));
                    }
                }
            }
        }
        
        if (!loop.sum_updates.empty()) {
            loop.sum_updates = iterator_detector.filterIteratorVariables(loop.sum_updates, ind_clause);
        }
        
        if (!loop.sum_updates.empty()) {
            bool has_negative_terms = false;
            if (!loop.sum_updates.empty()) {
                for (const auto& term : loop.sum_updates[0].terms) {
                    if (!term.is_positive) {
                        has_negative_terms = true;
                        break;
                    }
                }
            }
            if (!has_negative_terms) {
                loop.sum_updates.clear();
            }
        }

        loop.entry_clause = nullptr;
        if (_consequency.count(loop.loop_predicate)) {
            for (const auto* c : _consequency.at(loop.loop_predicate)) {
                if (c != loop.inductive_clause) { 
                    loop.entry_clause = c; 
                    break; 
                }
            }
        }
        
        loop.exit_clause = nullptr;
        if (_antecedency.count(loop.loop_predicate)) {
            for (const auto* c : _antecedency.at(loop.loop_predicate)) {
                if (c != loop.inductive_clause) { 
                    loop.exit_clause = c; 
                    break; 
                }
            }
        }
        
        if (!loop.sum_updates.empty() && loop.entry_clause && loop.exit_clause) {
            results.push_back(std::move(loop));
        }
    }
    
    return results;
}

// Debug helper function to print detected loops
void HyperGraph::debug_print_linear_loops(const std::vector<HyperGraph::LinearCombinationLoop>& loops) const {
    std::cout << "=== DETECTED LINEAR COMBINATION LOOPS ===" << std::endl;
    for (size_t i = 0; i < loops.size(); ++i) {
        const auto& loop = loops[i];
        std::cout << "Loop " << i << ":" << std::endl;
        std::cout << "  Predicate: " << loop.loop_predicate->name() << std::endl;
        std::cout << "  Sum updates: " << loop.sum_updates.size() << std::endl;
        
        for (size_t j = 0; j < loop.sum_updates.size(); ++j) {
            const auto& update = loop.sum_updates[j];
            std::cout << "    Update " << j << ": " << update.sum_var->name() 
                     << " (param index " << update.sum_var_arg_idx << ")" << std::endl;
            std::cout << "      Terms: " << update.terms.size() << std::endl;
            
            for (size_t k = 0; k < update.terms.size(); ++k) {
                const auto& term = update.terms[k];
                std::cout << "        Term " << k << ": " 
                         << (term.is_positive ? "+" : "-") << " ";
                
                // Enhanced coefficient printing
                if (term.coefficient) {
                    if (term.coefficient->kind() == TermKind::Constant) {
                        auto const_coeff = std::dynamic_pointer_cast<Constant>(term.coefficient);
                        if (const_coeff && !const_coeff->is_variable_constant()) {
                            // It's a literal constant - try to print it
                            std::cout << "coeff(literal)";
                        } else {
                            std::cout << "coeff(var)";
                        }
                    } else {
                        std::cout << "coeff(expr)";
                    }
                    std::cout << " * ";
                } else {
                    std::cout << "coeff(null) * ";
                }
                
                // Enhanced variable printing  
                if (term.variable) {
                    if (term.variable->kind() == TermKind::Constant) {
                        auto vc = std::dynamic_pointer_cast<VariableConstant>(term.variable);
                        if (vc) {
                            std::cout << vc->variable()->name() << "[" << vc->index() << "]";
                        } else {
                            auto const_var = std::dynamic_pointer_cast<Constant>(term.variable);
                            if (const_var && !const_var->is_variable_constant()) {
                                std::cout << "literal_const";
                            } else {
                                std::cout << "unknown_const";
                            }
                        }
                    } else if (term.variable->kind() == TermKind::OpApp) {
                        auto op_app = std::dynamic_pointer_cast<OperatorApplication>(term.variable);
                        if (op_app) {
                            std::cout << "expr(" << op_app->operat0r()->name() << ")";
                        } else {
                            std::cout << "expr(unknown)";
                        }
                    } else {
                        std::cout << "var(other_type)";
                    }
                } else {
                    std::cout << "var(null)";
                }
                std::cout << std::endl;
            }
        }
        std::cout << std::endl;
    }
    std::cout << "============================================" << std::endl;
}

void HyperGraph::simplify(hcvc::Context &context, Module* owner) {

    std::cout << "--- CLAUSES BEFORE TRANSFORMATION ---" << std::endl;
    for (const auto* clause : this->to_set()) {
        clause->dump();
    }
    std::cout << "------------------------------------" << std::endl;
    
    // Run our NEW linear combination transformation instead of old subtraction loops
    transform_linear_combination_loops(context, owner);
    
    std::cout << "--- CLAUSES AFTER TRANSFORMATION ---" << std::endl;
    for (const auto* clause : this->to_set()) {
        clause->dump();
    }
    std::cout << "------------------------------------" << std::endl;

    // Now we can simplify the clauses based on the new structure
    std::set<Weakness> weaknesses;
    for(auto [weakness, _]: _weakness_clause_map) {
      weaknesses.insert(weakness);
    }
    auto reachables = this->get_clauses(weaknesses).to_set();
    std::set<const Clause *> to_remove;
    for(auto clause: _clauses) {
      if(reachables.count(clause) == 0) {
        to_remove.insert(clause);
      }
    }
    for(auto clause: to_remove) {
      this->erase(clause);
    }

    while(true) {
      bool done = true;
      for(auto &predicate: _to_be_simplified) {
        if(!_antecedency[predicate].empty() && !_consequency[predicate].empty()) {
          done = false;
          auto clauses = _antecedency[predicate];
          auto subclauses = _consequency[predicate];
          for(auto &clause: clauses) {
            for(auto &subclause: subclauses) {
              auto newclause = substitute_clause(subclause, clause, context);
              Weakness clause_weakness;
              for(auto &[weakness, wclauses]: _weakness_clause_map) {
                if(wclauses.count(clause) > 0) {
                  wclauses.insert(newclause);
                  clause_weakness = weakness;
                }
              }
              this->add(newclause, clause_weakness);
            }
          }
          for(auto clause: clauses) {
            for(auto &[weakness, wclauses]: _weakness_clause_map) {
              if(wclauses.count(clause) > 0) {
                wclauses.erase(clause);
              }
            }
            this->erase(clause);
          }
          for(auto clause: subclauses) {
            this->erase(clause);
          }
        }
      }
      if(done) {
        break;
      }
    }
    while(true) {
      const Clause *clause = nullptr;
      const Predicate *P = nullptr;
      for(auto predicate: _to_be_simplified) {
        if(!_antecedency[predicate].empty()) {
          clause = *_antecedency[predicate].begin();
          P = predicate;
          break;
        }
      }
      if(clause == nullptr) {
        break;
      }
      while(true) {
        const Clause *subclause = nullptr;
        if(!_consequency[P].empty()) {
          subclause = *_consequency[P].begin();
        }
        if(subclause == nullptr) {
          break;
        }
        auto newclause = substitute_clause(subclause, clause, context);
        Weakness clause_weakness;
        for(auto &[weakness, clauses]: _weakness_clause_map) {
          if(clauses.count(clause) > 0) {
            clauses.erase(clause);
            clauses.insert(newclause);
            clause_weakness = weakness;
          }
        }
        this->add(newclause, clause_weakness);
        this->erase(subclause);
      }
      this->erase(clause);
    }
    
    std::set<const hcvc::Predicate *> predicate_to_eliminate;
    for(auto predicate: this->predicates()) {
      hcvc::Function *function = nullptr;
      if(predicate->kind() == PredicateKind::precondition) {
        function = ((FunctionPreconditionPredicate *) predicate)->function();
      } else if(predicate->kind() == PredicateKind::summary) {
        function = ((FunctionSummaryPredicate *) predicate)->function();
      }
      if(function != nullptr && function->is_specified()) {
        predicate_to_eliminate.emplace(predicate);
      }
    }
    while(true) {
      const hcvc::Clause *clause = nullptr;
      for(auto c: _clauses) {
        if(c->consequent()) {
          auto pred_app = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*c->consequent());
          if (pred_app.get() != nullptr && predicate_to_eliminate.count(pred_app->predicate()) > 0) {
            clause = c;
            break;
          }
        }
        if(clause != nullptr) break;
        for(auto &pred_app: c->antecedent_preds()) {
          auto casted_pred_app = std::dynamic_pointer_cast<hcvc::PredicateApplication>(pred_app);
          if(casted_pred_app.get() != nullptr && predicate_to_eliminate.count(casted_pred_app->predicate()) > 0) {
            clause = c;
            break;
          }
        }
      }
      if(clause == nullptr) {
        break;
      }
      
      auto new_phi = clause->phi();
      std::vector<hcvc::Expr> new_pred_apps;
      bool consequent_updated = false;
      bool consequent_is_pre = false;

      if(clause->consequent()) {
        auto predicate = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent())->predicate();
        hcvc::Function *function = nullptr;
        if(predicate->kind() == PredicateKind::precondition) function = ((FunctionPreconditionPredicate *) predicate)->function();
        else if(predicate->kind() == PredicateKind::summary) function = ((FunctionSummaryPredicate *) predicate)->function();
        consequent_is_pre = predicate->kind() == PredicateKind::precondition;
        if(predicate_to_eliminate.count(predicate) > 0) {
          auto consequent = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent());
          std::map<Expr, Expr> sub_map = {};
          for(unsigned long i = 0; i < consequent->predicate()->parameters().size(); i++) {
            sub_map[VariableConstant::create(consequent->predicate()->parameters()[i], 0, context)] = consequent->arguments()[i];
          }
          if(consequent->predicate()->kind() == PredicateKind::precondition) new_phi.push_back(!substitute(function->get_requirement(), sub_map));
          else if(consequent->predicate()->kind() == PredicateKind::summary) new_phi.push_back(!substitute(function->get_ensurement(), sub_map));
          consequent_updated = true;
        }
      }

      for(auto &pred_app: clause->antecedent_preds()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(pred_app);
        auto predicate = casted->predicate();
        hcvc::Function *function = nullptr;
        if(predicate->kind() == PredicateKind::precondition) function = ((FunctionPreconditionPredicate *) predicate)->function();
        else if(predicate->kind() == PredicateKind::summary) function = ((FunctionSummaryPredicate *) predicate)->function();
        if(predicate_to_eliminate.count(predicate) > 0) {
          std::map<Expr, Expr> sub_map = {};
          for(unsigned long i = 0; i < predicate->parameters().size(); i++) {
            sub_map[VariableConstant::create(predicate->parameters()[i], 0, context)] = casted->arguments()[i];
          }
          if(predicate->kind() == PredicateKind::precondition) new_phi.push_back(substitute(function->get_requirement(), sub_map));
          else if(predicate->kind() == PredicateKind::summary) new_phi.push_back(substitute(function->get_ensurement(), sub_map));
        } else {
          new_pred_apps.push_back(pred_app);
        }
      }

      auto new_clause = new Clause(new_pred_apps, new_phi, consequent_updated ? std::nullopt : clause->consequent(), context);
      std::set<Weakness> weaknesses_to_add;
      for(auto [weakness, clauses]: _weakness_clause_map) {
        if(clauses.count(clause) > 0) weaknesses_to_add.insert(weakness);
      }
      this->erase(clause);
      if(consequent_updated) this->add(new_clause, consequent_is_pre ? Weakness::assertion_violation : Weakness::specification_violation);
      if(!weaknesses_to_add.empty()) {
        for(auto weakness: weaknesses_to_add) this->add(new_clause, weakness);
      } else {
        this->add(new_clause);
      }
    }
    auto clauses = this->to_set();
    _init_clauses.clear();
    _ind_clauses.clear();
    _goal_clauses.clear();
    _antecedency.clear();
    _consequency.clear();
    for(auto clause: clauses) {
      this->add(clause);
    }
    for(auto [weakness, clss]: _weakness_clause_map) {
      std::set<const hcvc::Clause *> new_clss;
      for(auto cl: clss) {
        if(clauses.count(cl) > 0) new_clss.insert(cl);
      }
      _weakness_clause_map[weakness] = new_clss;
    }
    
    std::set<const Clause *> to_rmv;
    for(auto clause: this->_clauses) {
      if(is_false(clause->phi_expr())) to_rmv.insert(clause);
    }
    for(auto clause: to_rmv) {
      this->erase(clause);
    }
  }

}
