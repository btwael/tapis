//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "tapis/engines/hornice/teacher.hh"

#include <sstream>
#include <utility>
#include "smtface/solvers/z3/solver.hh"
#include "smtface/utils/array_to_epr.hh"
#include "hcvc/logic/smtface.hh"
#include "tapis/engines/bounds.hh"
#include "tapis/engines/options.hh"
#include "tapis/engines/outputs.hh"
#include "tapis/engines/statistics.hh"

namespace tapis::HornICE {

  //*-- LambdaDefinition
  LambdaDefinition::LambdaDefinition(const hcvc::Predicate *predicate, hcvc::Expr body)
      : _predicate(predicate), _body(std::move(body)) {}

  //*-- Teacher
  Teacher::Teacher(hcvc::Module *module, const hcvc::ClauseSet &clauses)
      : _module(module),
        _clause_set(clauses),
        _clauses(clauses.to_set()) {}

  const hcvc::State *_extract(const std::shared_ptr<hcvc::PredicateApplication> &pred_app, smtface::Model &model,
                              hcvc::StateManager &state_manager) {
    auto z3m = std::dynamic_pointer_cast<smtface::solvers::Z3Model>(model)->z3_model();
    //std::cout << z3m << "\n";
    std::map<std::string, z3::func_decl> interps;
    for(unsigned long i = 0; i < z3m.num_funcs(); i++) {
      if(z3m.get_func_decl(i).decl_kind() == Z3_decl_kind::Z3_OP_UNINTERPRETED) {
        auto symbol = z3m.get_func_decl(i).name();
        std::stringstream s;
        s << symbol;
        auto name = s.str();
        interps.emplace(name, z3m.get_func_decl(i));
      } else {
        interps.emplace(z3m.get_func_decl(i).name().str(), z3m.get_func_decl(i));
      }
    }
    std::map<const hcvc::Variable *, hcvc::Expr> values;
    for(unsigned long i = 0, size = pred_app->arguments().size(); i < size; i++) {
      auto param = pred_app->predicate()->parameters()[i];
      if(param->type()->is_array()) {
        auto it = find(pred_app->predicate()->parameters().begin(), pred_app->predicate()->parameters().end(),
                       param->size_variable());
        auto arr_type = (const hcvc::ArrayType *) param->type();
        auto index_of_size_variable = it - pred_app->predicate()->parameters().begin();
        auto array_size_expr = model->eval(hcvc::to_smtface(pred_app->arguments()[index_of_size_variable]));
        auto arr_size = std::stol(std::dynamic_pointer_cast<smtface::core::Value>(array_size_expr)->raw());
        std::vector<hcvc::Expr> array;
        auto array_var = std::dynamic_pointer_cast<hcvc::VariableConstant>(pred_app->arguments()[i]);
        auto default_value = [&]() -> z3::expr {
          if(arr_type->element_type()->is_int()) {
            return z3m.ctx().int_val(0);
          }
          if(arr_type->element_type()->is_bool()) {
            return z3m.ctx().bool_val(false);
          }
          return z3m.ctx().int_val(0);
        };
        for(long j = 0; j < arr_size; j++) {
          z3::expr v = default_value();
          if(array_var != nullptr && interps.count(array_var->name()) > 0) {
            v = z3m.eval((interps.at(array_var->name()))(j));
          } else if(array_var != nullptr) {
            z3::sort index_sort = z3m.ctx().int_sort();
            z3::sort element_sort = arr_type->element_type()->is_bool() ? z3m.ctx().bool_sort() : z3m.ctx().int_sort();
            z3::sort array_sort = z3m.ctx().array_sort(index_sort, element_sort);
            z3::expr array_expr = z3m.ctx().constant(array_var->name().c_str(), array_sort);
            v = z3m.eval(z3::select(array_expr, z3m.ctx().int_val(static_cast<int64_t>(j))));
          }

          if(v.is_bool()) {
            if(v.is_true()) {
              array.push_back(pred_app->context().get_true());
            } else {
              array.push_back(pred_app->context().get_false());
            }
          } else if(v.is_int() && v.is_numeral()) {
            array.push_back(
                hcvc::IntegerLiteral::get(std::to_string(v.get_numeral_int()),
                                          dynamic_cast<const hcvc::ArrayType *>(param->type())->element_type(),
                                          pred_app->context()));
          } else {
            if(arr_type->element_type()->is_int()) {
              array.push_back(hcvc::IntegerLiteral::get("0",
                                                        dynamic_cast<const hcvc::ArrayType *>(param->type())->element_type(),
                                                        pred_app->context()));
            } else if(arr_type->element_type()->is_bool()) {
              array.push_back(pred_app->context().get_false());
            }
          }
        }
        values[param] = hcvc::ArrayLiteral::get(array, param->type(), pred_app->context());
      } else if(param->type()->is_bool()) {
        auto eval = model->eval(hcvc::to_smtface(pred_app->arguments()[i]));
        values[param] = eval->is_true() ? pred_app->context().get_true() : pred_app->context().get_false();
      } else if(param->type()->is_int()) {
        auto eval = model->eval(hcvc::to_smtface(pred_app->arguments()[i]));
        values[param] = hcvc::IntegerLiteral::get(std::dynamic_pointer_cast<smtface::core::Value>(eval)->raw(),
                                                  param->type(), pred_app->context());
      }
    }
    return state_manager.get_state(pred_app->predicate(), values);
  }

  hcvc::Expr get_type_constraints(const hcvc::Clause *clause, unsigned long max_size,
                                  const std::function<hcvc::Expr(const hcvc::Expr &)> &size_restriction_func,
                                  const std::function<hcvc::Expr(const hcvc::Expr &)> &array_restriction_func) {
    auto res = clause->context().get_true();
    for(const auto &pred_app_expr: clause->antecedent_preds()) {
      auto pred_app = std::dynamic_pointer_cast<hcvc::PredicateApplication>(pred_app_expr);
      for(unsigned long i = 0, size = pred_app->arguments().size(); i < size; i++) {
        if(pred_app->arguments()[i]->type()->is_array()) {
          auto it = find(pred_app->predicate()->parameters().begin(), pred_app->predicate()->parameters().end(),
                         pred_app->predicate()->parameters()[i]->size_variable());
          auto index_of_size_variable = it - pred_app->predicate()->parameters().begin();
          assert(i != index_of_size_variable);
          auto gt_0 = (pred_app->arguments()[index_of_size_variable] >
                       hcvc::IntegerLiteral::get("0", pred_app->arguments()[index_of_size_variable]->type(),
                                                 clause->context()));
          res = res && gt_0 && size_restriction_func(pred_app->arguments()[index_of_size_variable]);
          res = res && array_restriction_func(pred_app->arguments()[i]);
          if(pred_app->arguments()[index_of_size_variable]->type()->is_array()) {
            std::cout << "IMPL-UNREACH" << "\n";
            exit(10);
          }
        } else if(!pred_app->arguments()[i]->type()->is_bool() &&
                  pred_app->arguments()[i]->type()->is_int()) {
          auto sort = dynamic_cast<const hcvc::IntType *>(pred_app->arguments()[i]->type());
          if(sort->signedness() == hcvc::Signedness::Unsigned) {
            auto gt_0 = clause->context().apply(">=", {pred_app->arguments()[i],
                                                       hcvc::IntegerLiteral::get("0", sort, clause->context())});
            res = res && gt_0;
          }
        }
      }
    }
    if(clause->consequent()) {
      auto pred_app = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent());
      for(unsigned long i = 0, size = pred_app->arguments().size(); i < size; i++) {
        if(pred_app->arguments()[i]->type()->is_array()) {
          auto it = find(pred_app->predicate()->parameters().begin(), pred_app->predicate()->parameters().end(),
                         pred_app->predicate()->parameters()[i]->size_variable());
          auto index_of_size_variable = it - pred_app->predicate()->parameters().begin();
          assert(i != index_of_size_variable);
          auto gt_0 = (pred_app->arguments()[index_of_size_variable] >
                       hcvc::IntegerLiteral::get("0", pred_app->arguments()[index_of_size_variable]->type(),
                                                 clause->context()));
          res = res && gt_0 && size_restriction_func(pred_app->arguments()[index_of_size_variable]);
          res = res && array_restriction_func(pred_app->arguments()[i]);
          if(pred_app->arguments()[index_of_size_variable]->type()->is_array()) {
            std::cout << "IMPL-UNREACH" << "\n";
            exit(10);
          }
        } else if(!pred_app->arguments()[i]->type()->is_bool() &&
                  pred_app->arguments()[i]->type()->is_int()) {
          auto sort = dynamic_cast<const hcvc::IntType *>(pred_app->arguments()[i]->type());
          if(sort->signedness() == hcvc::Signedness::Unsigned) {
            auto gt_0 = clause->context().apply(">=", {pred_app->arguments()[i],
                                                       hcvc::IntegerLiteral::get("0", sort, clause->context())});
            res = res && gt_0;
          }
        }
      }
    }
    return res;
  }

  std::set<const hcvc::Implication *>
  Teacher::check(const std::unordered_map<const hcvc::Predicate *, LambdaDefinition> &hypothesis) {
    while(true) {
      std::set<const hcvc::Implication *> res;
      if(get_options().ice.qdt.bounded_data_values) {
        res = _check(hypothesis, [&](const hcvc::Expr &size) -> hcvc::Expr {
          return size->context().apply("<=",
                                       {size, hcvc::IntegerLiteral::get(std::to_string(get_bounds()._max_array_size),
                                                                        size->type(), size->context())});
        }, [&](const hcvc::Expr &array) {
          auto &context = array->context();
          auto f = context.get_true();
          auto array_type = (const hcvc::ArrayType *) array->type();
          if(!array_type->element_type()->is_int()) {
            return f;
          }
          auto N = hcvc::IntegerLiteral::get(std::to_string(get_bounds()._max_array_value),
                                             context.type_manager().uint_type(),
                                             context);
          for(unsigned long i = 0; i < get_bounds()._max_array_size; i++) {
            auto idx = hcvc::IntegerLiteral::get(std::to_string(i), context.type_manager().uint_type(), context);
            f = f && context.apply("<=", {context.apply("[]", {array, idx}), N})
                && context.apply(">=", {context.apply("[]", {array, idx}), -N});
          }
          auto length = hcvc::VariableConstant::create(
              std::dynamic_pointer_cast<hcvc::VariableConstant>(array)->variable()->size_variable(), 0, context);
          auto zero = hcvc::IntegerLiteral::get(std::to_string(0), context.type_manager().int_type(), context);
          auto q = hcvc::Constant::create("!!q!", context.type_manager().int_type(), context);
          auto outofrange = hcvc::QuantifiedFormula::create(
              hcvc::Quantifier::ForAll,
              {q},
              context.apply("=>",
                            {context.apply("or", {zero > q, length <= q}),
                             context.apply("[]", {array, q}) == zero}), context);
          //std::cout << outofrange << "\n";
          return f && outofrange;
        });
        if(!res.empty()) {
          return res;
        }
        res = _check(hypothesis, [&](const hcvc::Expr &size) -> hcvc::Expr {
          return size->context().apply("<=",
                                       {size, hcvc::IntegerLiteral::get(std::to_string(get_bounds()._max_array_size),
                                                                        size->type(), size->context())});
        }, [&](const hcvc::Expr &array) {
          auto &context = array->context();
          auto f = context.get_true();
          auto array_type = (const hcvc::ArrayType *) array->type();
          if(!array_type->element_type()->is_int()) {
            return f;
          }
          auto length = hcvc::VariableConstant::create(
              std::dynamic_pointer_cast<hcvc::VariableConstant>(array)->variable()->size_variable(), 0, context);
          auto zero = hcvc::IntegerLiteral::get(std::to_string(0), context.type_manager().int_type(), context);
          auto q = hcvc::Constant::create("!!q!", context.type_manager().int_type(), context);
          auto outofrange = hcvc::QuantifiedFormula::create(
              hcvc::Quantifier::ForAll,
              {q},
              context.apply("=>",
                            {context.apply("or", {zero > q, length <= q}),
                             context.apply("[]", {array, q}) == zero}), context);
          //std::cout << outofrange << "\n";
          return outofrange;
        });
        if(!res.empty()) {
          get_bounds()._max_array_value++;
          continue;
        }
      } else {
        res = _check(hypothesis, [&](const hcvc::Expr &size) -> hcvc::Expr {
          return size->context().apply("<=",
                                       {size, hcvc::IntegerLiteral::get(std::to_string(get_bounds()._max_array_size),
                                                                        size->type(), size->context())});
        }, [&](const hcvc::Expr &array) {
          auto &context = array->context();
          auto length = hcvc::VariableConstant::create(
              std::dynamic_pointer_cast<hcvc::VariableConstant>(array)->variable()->size_variable(), 0, context);
          auto zero = hcvc::IntegerLiteral::get(std::to_string(0), context.type_manager().int_type(), context);
          auto q = hcvc::Constant::create("!!q!", context.type_manager().int_type(), context);
          auto outofrange = hcvc::QuantifiedFormula::create(
              hcvc::Quantifier::ForAll,
              {q},
              context.apply("=>",
                            {context.apply("or", {zero > q, length <= q}),
                             context.apply("[]", {array, q}) == zero}), context);
          //std::cout << outofrange << "\n";
          return outofrange;
        });
        if(!res.empty()) {
          return res;
        }
      }
      auto hp = hypothesis;
      for(auto &[p, h]: hp) {
        hp.at(p)._body = hp.at(p)._body && get_outputs().preanalysis_invariants.at(p);
      }
      bool is_inv = _check(hp);
      if(is_inv) {
        return res;
      }
#ifndef NDEBUG
      std::cout << "=======" << get_bounds()._max_array_size << "\n";
#endif
      get_bounds()._max_array_size++;
    }
  }

  const hcvc::Implication *Teacher::_check(const hcvc::Clause *clause,
                                           const std::unordered_map<const hcvc::Predicate *, LambdaDefinition> &hypothesis,
                                           const std::function<hcvc::Expr(
                                               const hcvc::Expr &)> &size_restriction_func,
                                           const std::function<hcvc::Expr(
                                               const hcvc::Expr &)> &array_restriction_func) {
    auto lhs = clause->phi_expr();
    auto rhs = clause->context().get_false();
    auto type_constraints = get_type_constraints(clause, get_bounds()._max_array_size, size_restriction_func,
                                                 array_restriction_func);
    for(const auto &antecedent: clause->antecedent_preds()) {
      auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(antecedent);
      std::map<hcvc::Expr, hcvc::Expr> sub_map;
      for(unsigned long i = 0, size = casted->predicate()->parameters().size(); i < size; i++) {
        auto param = casted->predicate()->parameters()[i];
        sub_map[hcvc::VariableConstant::create(param, 0, casted->context())] = casted->arguments()[i];
      }
      lhs = lhs && hcvc::substitute(hypothesis.at(casted->predicate()).body(), sub_map);
      if(get_options().absint.perform) {
        lhs = lhs && hcvc::substitute(get_outputs().preanalysis_invariants.at(casted->predicate()), sub_map);
      }
    }
    if(clause->consequent()) {
      auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent());
      std::map<hcvc::Expr, hcvc::Expr> sub_map;
      for(unsigned long i = 0, size = casted->predicate()->parameters().size(); i < size; i++) {
        auto param = casted->predicate()->parameters()[i];
        sub_map[hcvc::VariableConstant::create(param, 0, casted->context())] = casted->arguments()[i];
      }
      rhs = hcvc::substitute(hypothesis.at(casted->predicate()).body(), sub_map);
    }
    if(hcvc::is_true(rhs) || hcvc::is_false(lhs)) {
      return nullptr;
    }
#ifndef NDEBUG
    std::cout << "Teacher.check [Fixed N]? " << lhs << " => " << rhs << "\n";
#endif
    smtface::push_context();
    smtface::solvers::Z3Solver solver(smtface::current_context());
    //std::cout << smtface::ToString(smtface::utils::array_to_epr((!smtface::Implies(hcvc::to_smtface(lhs), hcvc::to_smtface(rhs))) && hcvc::to_smtface(type_constraints))) << "\n";
    auto res = solver.get_model(
        smtface::utils::array_to_epr(
            (!smtface::Implies(hcvc::to_smtface(lhs), hcvc::to_smtface(rhs))) && hcvc::to_smtface(type_constraints)));
    get_statistics().smt.queries++;
    if(res) {
      auto model = *res;
      //std::cout << std::dynamic_pointer_cast<smtface::solvers::Z3Model>(model)->z3_model() << "\n";
      std::vector<const hcvc::State *> antecedents;
      const hcvc::State *consequent = nullptr;
      for(const auto &antecedent: clause->antecedent_preds()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(antecedent);
        antecedents.push_back(_extract(casted, model, _state_manager));
      }
      if(clause->consequent()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent());
        consequent = _extract(casted, model, _state_manager);
      }
      auto impl = _state_manager.get_implication(clause, antecedents, consequent);
#ifndef NDEBUG
      std::cout << "    - ";
      unsigned long i = 0;
      if(!antecedents.empty()) {
        for(auto state: antecedents) {
          std::cout << state->hash();
          if(i != antecedents.size() - 1) {
            std::cout << ", ";
          }
        }
      } else {
        std::cout << "true";
      }
      std::cout << " => ";
      if(consequent != nullptr) {
        std::cout << consequent->hash() << "\n";
      } else {
        std::cout << "false" << "\n";
      }
#endif
      smtface::pop_context();
      return impl;
    }
    smtface::pop_context();
    return nullptr;
  }

  std::set<const hcvc::Implication *>
  Teacher::_check(const std::unordered_map<const hcvc::Predicate *, LambdaDefinition> &hypothesis,
                  const std::function<hcvc::Expr(const hcvc::Expr &)> &size_restriction_func,
                  const std::function<hcvc::Expr(const hcvc::Expr &)> &array_restriction_func) {
    std::set<const hcvc::Implication *> counterexamples;
    for(const auto clause: _clauses) {
      auto cex = _check(clause, hypothesis, size_restriction_func, array_restriction_func);
      if(cex != nullptr) {
        counterexamples.insert(cex);
        if(!get_options().ice.teacher.multiple_counterexamples) {
          return counterexamples;
        }
      }
    }
    return counterexamples;
  }

  bool Teacher::_check(const std::unordered_map<const hcvc::Predicate *, LambdaDefinition> &hypothesis) {
    for(const auto clause: _clauses) {
      auto lhs = clause->phi_expr();
      auto rhs = clause->context().get_false();
      auto type_constraints = get_type_constraints(clause, 0, [=](const hcvc::Expr &size) {
        return size->context().get_true();
      }, [=](const hcvc::Expr &array) {
        return array->context().get_true();
      });
      for(const auto &antecedent: clause->antecedent_preds()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(antecedent);
        std::map<hcvc::Expr, hcvc::Expr> sub_map;
        for(unsigned long i = 0, size = casted->predicate()->parameters().size(); i < size; i++) {
          auto param = casted->predicate()->parameters()[i];
          sub_map[hcvc::VariableConstant::create(param, 0, casted->context())] = casted->arguments()[i];
        }
        lhs = lhs && hcvc::substitute(hypothesis.at(casted->predicate()).body(), sub_map);
      }
      if(clause->consequent()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent());
        std::map<hcvc::Expr, hcvc::Expr> sub_map;
        for(unsigned long i = 0, size = casted->predicate()->parameters().size(); i < size; i++) {
          auto param = casted->predicate()->parameters()[i];
          sub_map[hcvc::VariableConstant::create(param, 0, casted->context())] = casted->arguments()[i];
        }
        rhs = hcvc::substitute(hypothesis.at(casted->predicate()).body(), sub_map);
      }
#ifndef NDEBUG
      std::cout << "Teacher.check [Forall N]? " << lhs << " => " << rhs << "\n";
#endif
      smtface::push_context();
      smtface::solvers::Z3Solver solver(smtface::current_context());
      //std::cout << smtface::ToString(smtface::utils::array_to_epr((!smtface::Implies(hcvc::to_smtface(lhs), hcvc::to_smtface(rhs))) && hcvc::to_smtface(type_constraints))) << "\n";
      auto res = solver.get_model(
          smtface::utils::array_to_epr(
              (!smtface::Implies(hcvc::to_smtface(lhs), hcvc::to_smtface(rhs))) && hcvc::to_smtface(type_constraints)));
      get_statistics().smt.queries++;
      if(res) {
        auto m = std::dynamic_pointer_cast<smtface::solvers::Z3Model>(*res);
#ifndef NDEBUG
        std::cout << m->z3_model() << "\n";
#endif
        smtface::pop_context();
        return false;
      }
      smtface::pop_context();
    }
    return true;
  }

  hcvc::Expr get_formula(const std::set<const hcvc::State *> &states, hcvc::Context &context) {
    auto res = context.get_false();
    for(auto state: states) {
      res = res || state->to_formula(context);
    }
    return res;
  }

}
