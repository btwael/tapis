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



void HyperGraph::transform_linear_combination_loops(Context &context, Module* owner) {
    // Phase 1: Analysis - Find loops that require transformation and create a plan.
    auto all_loops = find_linear_combination_loops(owner);
    if (all_loops.empty()) {
        return; // No loops with negative terms were found. Nothing to do.
    }

    struct TransformPlan {
        Predicate* new_predicate = nullptr;
        std::vector<Variable*> accumulators; 
        const LinearCombinationLoop* loop_info = nullptr;
    };
    std::map<const Predicate*, TransformPlan> transform_plans;

    for (const auto& loop : all_loops) {
        if (transform_plans.count(loop.loop_predicate)) continue;
        TransformPlan plan;
        plan.loop_info = &loop;
        for (const auto& sum_update : loop.sum_updates) {
            std::string acc_name = "acc_" + sum_update.sum_var->name() + "_" + loop.loop_predicate->name();
            auto acc_var = new Variable(acc_name, sum_update.sum_var->type(), owner->context());
            acc_var->set_is_data();
            plan.accumulators.push_back(acc_var);
        }
        auto new_params = loop.loop_predicate->parameters();
        for (auto acc_var : plan.accumulators) { new_params.push_back(acc_var); }
        plan.new_predicate = InvariantPredicate::create(loop.owner_function, loop.loop_predicate->name(), new_params);
        transform_plans[loop.loop_predicate] = plan;
    }
    
    // Phase 2: Clause Rewriting - Build a new, transformed set of clauses on the side.
    std::vector<const Clause*> final_clauses;
    std::map<const Clause*, std::set<Weakness>> clause_weakness_map;

    for (const auto* clause : this->to_set()) {
        const Clause* new_clause = clause;
        
        bool is_involved = false;
        for(const auto& app_expr : clause->antecedent_preds()) {
            auto app = std::dynamic_pointer_cast<PredicateApplication>(app_expr);
            if (app && transform_plans.count(app->predicate())) { is_involved = true; break; }
        }
        if (!is_involved && clause->consequent()) {
            auto app = std::dynamic_pointer_cast<PredicateApplication>(*clause->consequent());
            if (app && transform_plans.count(app->predicate())) { is_involved = true; }
        }

        if (is_involved) {
            auto new_antecedents = clause->antecedent_preds();
            auto new_phi = clause->phi();
            auto new_consequent = clause->consequent();

            // --- Step 1: Transform Antecedent(s) if necessary (Exit/Helper logic) ---
            Predicate* antecedent_pred_to_transform = nullptr;
            for(const auto& app_expr : new_antecedents) {
                auto app = std::dynamic_pointer_cast<PredicateApplication>(app_expr);
                if (app && transform_plans.count(app->predicate())) {
                    antecedent_pred_to_transform = app->predicate();
                    break;
                }
            }



if (antecedent_pred_to_transform) {
    const auto& ant_plan = transform_plans.at(antecedent_pred_to_transform);
    

    std::map<Expr, Expr> ssa_sub_map;       // Map from old var to new SSA var, e.g., |s@0| -> |s@1|
    std::vector<Expr> ssa_equalities;      // List of new equalities, e.g., (= |s@1| (- |s@0| |acc@0|))


    for(const auto& app_expr : new_antecedents) {
        auto ant_app = std::dynamic_pointer_cast<PredicateApplication>(app_expr);
        if(ant_app && ant_app->predicate() == antecedent_pred_to_transform) {
            for (size_t j = 0; j < ant_plan.loop_info->sum_updates.size(); ++j) {
                const auto& sum_update = ant_plan.loop_info->sum_updates[j];
                auto accumulator_var = ant_plan.accumulators[j];
                auto acc_at_exit = VariableConstant::create(accumulator_var, 0, context);
                auto s_at_exit = ant_app->arguments()[sum_update.sum_var_arg_idx];

                // 1. Create a new SSA version of the variable.
                auto s_corrected_vc = std::dynamic_pointer_cast<VariableConstant>(s_at_exit)->next();

                // 2. Define the update expression.
                auto corrected_s_val = context.apply("-", {s_at_exit, acc_at_exit});
                
                // 3. Store the defining equality and the substitution rule.
                ssa_equalities.push_back(s_corrected_vc == corrected_s_val);
                ssa_sub_map[s_at_exit] = s_corrected_vc;
            }
        }
    }

    // 4. Apply the correct SSA substitution to the rest of the clause.
    for (size_t k = 0; k < new_phi.size(); ++k) {
        new_phi[k] = substitute(new_phi[k], ssa_sub_map);
    }
    if (new_consequent.has_value()) {
        new_consequent = substitute(new_consequent.value(), ssa_sub_map);
    }

    // 5. Add the new defining equalities to the clause's body.
    new_phi.insert(new_phi.end(), ssa_equalities.begin(), ssa_equalities.end());


    for (size_t k=0; k < new_antecedents.size(); ++k) {
        auto app_to_modify = std::dynamic_pointer_cast<PredicateApplication>(new_antecedents[k]);
            if(app_to_modify && app_to_modify->predicate() == antecedent_pred_to_transform) {
            auto args = app_to_modify->arguments(); 
            for (auto acc_var : ant_plan.accumulators) args.push_back(VariableConstant::create(acc_var, 0, context));
            new_antecedents[k] = std::make_shared<PredicateApplication>(ant_plan.new_predicate, args, context);
            }
    }
}
            
            // --- Step 2: Transform Consequent if necessary (Entry/Inductive logic) ---
            auto cons_app = new_consequent ? std::dynamic_pointer_cast<PredicateApplication>(*new_consequent) : nullptr;
            if (cons_app && transform_plans.count(cons_app->predicate())) {
                const auto& cons_plan = transform_plans.at(cons_app->predicate());
                
                bool is_inductive_for_consequent = false;
                for(const auto& ant_expr : clause->antecedent_preds()) {
                    auto ant_app = std::dynamic_pointer_cast<PredicateApplication>(ant_expr);
                    if (ant_app && ant_app->predicate() == cons_app->predicate()) {
                        is_inductive_for_consequent = true;
                        break;
                    }
                }

                if (is_inductive_for_consequent) { 
                    const auto& sum_update = cons_plan.loop_info->sum_updates[0];
                    std::vector<Expr> temp_phi;
                    for(const auto& constraint : new_phi){
                        auto eq_op = std::dynamic_pointer_cast<OperatorApplication>(constraint);
                        bool is_our_update_rule = false;
                        if(eq_op.get() != nullptr && eq_op->arguments().size() > 0){
                           auto vc_lhs = std::dynamic_pointer_cast<VariableConstant>(eq_op->arguments()[0]);
                           if(vc_lhs.get() != nullptr && vc_lhs->variable() == sum_update.sum_var) is_our_update_rule = true;
                        }
                        if(!is_our_update_rule) temp_phi.push_back(constraint);
                    }
                    new_phi = temp_phi;
                    
                    std::vector<Expr> pos, neg;
                    for(const auto& t : sum_update.terms) if(t.is_positive) pos.push_back(t.variable); else neg.push_back(t.variable);
                    Expr s_rhs = sum_update.sum_old_expr; for(const auto& p:pos) s_rhs = context.apply("+",{s_rhs,p});
                    new_phi.push_back(context.apply("=", {sum_update.sum_new_expr, s_rhs}));
                    
                    auto acc_old = VariableConstant::create(cons_plan.accumulators[0], 0, context);
                    auto acc_new = VariableConstant::create(cons_plan.accumulators[0], 1, context);
                    Expr acc_rhs = acc_old; for(const auto& n:neg) acc_rhs = context.apply("+",{acc_rhs,n});
                    new_phi.push_back(context.apply("=", {acc_new, acc_rhs}));

                    auto cons_args = cons_app->arguments();
                    cons_args.push_back(acc_new);
                    new_consequent = std::make_shared<PredicateApplication>(cons_plan.new_predicate, cons_args, context);

                } else { 
                    for (auto acc_var : cons_plan.accumulators) {
                        auto acc_init = VariableConstant::create(acc_var, 0, context);
                        new_phi.push_back(context.apply("=", {acc_init, IntegerLiteral::get("0", acc_var->type(), context)}));
                    }
                    auto args = cons_app->arguments();
                    for (auto acc_var : cons_plan.accumulators) args.push_back(VariableConstant::create(acc_var, 0, context));
                    new_consequent = std::make_shared<PredicateApplication>(cons_plan.new_predicate, args, context);
                }
            }

            new_clause = new Clause(new_antecedents, new_phi, new_consequent, context);
        }

        final_clauses.push_back(new_clause);
        for (auto const& [weakness, clauses_with_weakness] : _weakness_clause_map) {
            if (clauses_with_weakness.count(clause)) {
                clause_weakness_map[new_clause].insert(weakness);
            }
        }
    }

    // Phase 3: Atomically rebuild the entire hypergraph.
    _clauses.clear(); _init_clauses.clear(); _ind_clauses.clear(); _goal_clauses.clear();
    _antecedency.clear(); _consequency.clear(); _weakness_clause_map.clear();
    for (const auto* cl : final_clauses) {
        if (clause_weakness_map.count(cl)) {
            for (const auto& weakness : clause_weakness_map.at(cl)) this->add(cl, weakness);
        } else {
            this->add(cl);
        }
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
    
    // Recursively find and collect all variable constant terms
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
    
    // Find sum variable based on LHS variable match
    std::pair<Expr, std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>> 
    extractSumVariableAndTerms(const std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>& all_terms, const Expr& lhs_expr) {
        
        Expr sum_var; 
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
            return {Expr{}, all_terms};
        }
        
        // Find the term that matches the target variable
        for (const auto& term : all_terms) {
            bool is_sum_var = false;
            
            if (term.variable->kind() == TermKind::Constant) {
                auto vc = std::dynamic_pointer_cast<VariableConstant>(term.variable);
                if (vc && vc->variable() == target_var) {
                    std::cout << "    Found matching sum variable term: " << vc->variable()->name() << "[" << vc->index() << "]" << std::endl;
                    if (sum_var.get() == nullptr) { 
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
    
    // parsing for nested expressions
    std::pair<Expr, std::vector<HyperGraph::LinearCombinationLoop::LinearTerm>> parseUpdate(const Expr& rhs_expr, const Expr& lhs_expr) {
        std::cout << "  Parsing RHS with kind=" << (int)rhs_expr->kind() << std::endl;
        
        if (rhs_expr->kind() != TermKind::OpApp) {
            std::cout << "  Not an operation - skipping" << std::endl;
            return {Expr{}, {}}; 
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
            return false;
        }
        
        auto vc = std::dynamic_pointer_cast<VariableConstant>(term.variable);
        if (vc) {
            return false;
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
        
        if (antecedent_pred_app.get() == nullptr || consequent_pred_app.get() == nullptr || 
            antecedent_pred_app->predicate() != consequent_pred_app->predicate()) continue;
            
        loop.loop_predicate = antecedent_pred_app->predicate();
        loop.owner_function = owner->get_function_owner(loop.loop_predicate);
        if (loop.owner_function == nullptr) continue;
        
        for (const auto& constraint : ind_clause->phi()) {
            auto eq_op = std::dynamic_pointer_cast<OperatorApplication>(constraint);
            if (eq_op.get() == nullptr || eq_op->operat0r()->name() != "=" || eq_op->arguments().size() != 2) continue;
            
            auto lhs = eq_op->arguments()[0];
            auto rhs = eq_op->arguments()[1];
            
            auto [sum_old_expr, terms] = parser.parseUpdate(rhs, lhs);
            
            if (sum_old_expr && !terms.empty()) {
                auto vc_new = std::dynamic_pointer_cast<VariableConstant>(lhs);
                auto vc_old = std::dynamic_pointer_cast<VariableConstant>(sum_old_expr);
                
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
