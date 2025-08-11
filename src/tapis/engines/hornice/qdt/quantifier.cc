//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "tapis/engines/hornice/qdt/quantifier.hh"

#include "hcvc/program/variable.hh"
#include "tapis/engines/options.hh"
#include <cassert>


namespace tapis::HornICE::qdt {

  //*-- QuantifierManager
  QuantifierManager::QuantifierManager(unsigned long quantifier_per_array)
      : _quantifier_per_array(quantifier_per_array),
        _context(nullptr) {}

  QuantifierManager::~QuantifierManager() {
  }

  void QuantifierManager::set_predicates(const std::set<const hcvc::Predicate *> &predicates) {
    _predicates = predicates;
  }

void QuantifierManager::setup() {
    assert(_context != nullptr && "Context must be set before setup");

    for (const auto* predicate : _predicates) {
        _quantifiers[predicate] = std::vector<QuantifierInfo *>();
        _quantifier_variables[predicate] = std::set<const hcvc::Variable *>();
        _accessor_variables[predicate] = std::set<const hcvc::Variable *>();
        std::set<const hcvc::Variable *> _skip_variables;
        for (auto var: predicate->parameters()) {
            if (var->type()->is_array() && var->is_shadow()) {
                _skip_variables.insert(var);
            }
        }

        std::set<const hcvc::Variable *> processed_arrays;
        const auto& shared_groups = get_options().ice.qdt.shared_quantifier_groups;

        // 1. === Handle Shared Quantifier Groups First ===
        if (!shared_groups.empty()) {
            for (const auto& group : shared_groups) {
                std::vector<const hcvc::Variable *> shared_quantifier_vars;
                for (unsigned long j = 0; j < _quantifier_per_array; ++j) {
                    auto name = "!k" + std::to_string(_qc++);
                    auto shared_k = hcvc::Variable::create(name, context().type_manager().int_type(), *_context, true);
                    shared_quantifier_vars.push_back(shared_k);
                }

                std::vector<const hcvc::Variable*> arrays_in_group;
                for (auto parameter : predicate->parameters()) {
                    if (parameter->type()->is_array() && group.count(parameter->name())) {
                        arrays_in_group.push_back(parameter);
                    }
                }

                for (auto array_param : arrays_in_group) {
                    if (_skip_variables.count(array_param) > 0 && get_options().ice.qdt.abstract_summary_input_arrays) {
                        continue;
                    }
                    for (const auto& shared_k : shared_quantifier_vars) {
                        auto qi = new QuantifierInfo();
                        qi->quantifier = shared_k;
                        qi->accessor = hcvc::Variable::create("!" + array_param->name() + shared_k->name(),
                                                              dynamic_cast<const hcvc::ArrayType *>(array_param->type())->element_type(),
                                                              *_context,
                                                              true);
                        qi->predicate = predicate;
                        qi->array = array_param;
                        qi->size_variable = array_param->size_variable();

                        _quantifiers[predicate].push_back(qi);
                        _array_quantifiers[predicate][array_param].push_back(qi);
                        _quantifier_variables[predicate].insert(qi->quantifier);
                        _accessor_variables[predicate].insert(qi->accessor);
                    }
                    processed_arrays.insert(array_param);
                }
            }
        }

        for(auto parameter : predicate->parameters()) {
            if(parameter->type()->is_array() && processed_arrays.find(parameter) == processed_arrays.end()) {
                if(_skip_variables.count(parameter) > 0 && get_options().ice.qdt.abstract_summary_input_arrays) {
                    continue;
                }
                unsigned long j = 0;
                while(j < _quantifier_per_array) {
                    auto qi = new QuantifierInfo();
                    auto name = "!k" + std::to_string(_qc++);
                    qi->quantifier = hcvc::Variable::create(name, context().type_manager().int_type(), *_context, true);
                    _quantifier_variables[predicate].insert(qi->quantifier);
                    qi->accessor = hcvc::Variable::create("!" + parameter->name() + name,
                                                          dynamic_cast<const hcvc::ArrayType *>(parameter->type())->element_type(),
                                                          *_context,
                                                          true);
                    _accessor_variables[predicate].insert(qi->accessor);
                    qi->predicate = predicate;
                    qi->array = parameter;
                    qi->size_variable = parameter->size_variable();
                    _quantifiers[predicate].push_back(qi);
                    _array_quantifiers[predicate][parameter].push_back(qi);
                    j++;
                }
            }
        }
        
        for(auto parameter : predicate->parameters()) {
            if(parameter->type()->is_array()) {
                for(auto parai: predicate->parameters()) {
                    if(!parai->is_data() && parai->type()->is_int()) {
                        auto acc_var = hcvc::Variable::create("!" + parameter->name() + "!" + parai->name(),
                                                              dynamic_cast<const hcvc::ArrayType *>(parameter->type())->element_type(),
                                                              *_context, true);
                        _accessor_variables[predicate].insert(acc_var);
                        auto T = hcvc::VariableConstant::create(parameter, 0, *_context);
                        auto k = hcvc::VariableConstant::create(parai, 0, *_context);
                        auto Tk = hcvc::VariableConstant::create(acc_var, 0, *_context);
                        _sub_maps[predicate][Tk] = _context->apply("[]", {T, k});
                        auto qi = new QuantifierInfo();
                        qi->quantifier = parai;
                        qi->accessor = acc_var;
                        qi->predicate = predicate;
                        qi->array = parameter;
                        qi->size_variable = parameter->size_variable();
                        _injected_access_variables[predicate].push_back(qi);
                    }
                }
            }
        }

        auto restrictions = _context->get_true();
        
        for (auto const& [array, quantifiers] : _array_quantifiers[predicate]) {
            for (unsigned long i = 0; i < quantifiers.size() - 1; i++) {
                auto qi1 = quantifiers[i];
                auto k1 = hcvc::VariableConstant::create(qi1->quantifier, 0, *_context);
                auto qi2 = quantifiers[i+1];
                auto k2 = hcvc::VariableConstant::create(qi2->quantifier, 0, *_context);
                restrictions = restrictions && _context->apply("<=", {k1, k2});
            }
        }

        // Build substitution maps. This must iterate over all QIs because accessors are unique.
        for (auto qi : _quantifiers[predicate]) {
            auto k = hcvc::VariableConstant::create(qi->quantifier, 0, *_context);
            auto T = hcvc::VariableConstant::create(qi->array, 0, *_context);
            auto Tk = hcvc::VariableConstant::create(qi->accessor, 0, *_context);
            _sub_maps[predicate][Tk] = _context->apply("[]", {T, k});
        }

        // Build quantifier list and range restrictions. This must iterate over UNIQUE quantifiers.
        for (const auto* quant_var : _quantifier_variables[predicate]) {
            auto k = hcvc::VariableConstant::create(quant_var, 0, *_context);
            _quantifier_exprs[predicate].push_back(k);

            // Find an associated QI to get the size variable
            const hcvc::Variable* size_var = nullptr;
            for (auto qi : _quantifiers[predicate]) {
                if (qi->quantifier == quant_var) {
                    size_var = qi->size_variable;
                    break;
                }
            }

            if (size_var) {
                auto size = hcvc::VariableConstant::create(size_var, 0, *_context);
                restrictions = restrictions &&
                             _context->apply("<=", {hcvc::IntegerLiteral::get("0", k->type(), *_context), k})
                             && _context->apply("<", {k, size});
            }
        }
        _restrictions[predicate] = restrictions;
    }
}

  void QuantifierManager::increase(unsigned long N) {
    for(auto predicate: _predicates) {
      std::set<const hcvc::Variable *> _skip_variables;
      for(auto var: predicate->parameters()) {
        if(var->type()->is_array() && var->is_shadow()) {
          _skip_variables.insert(var);
        }
      }

      for(unsigned long i = 0, size = predicate->parameters().size(); i < size; i++) {
        auto parameter = predicate->parameters()[i];
        if(parameter->type()->is_array()) {
          if(_skip_variables.count(parameter) > 0) {
            if(get_options().ice.qdt.abstract_summary_input_arrays) {
              continue;
            }
          }
          unsigned long j = 0;
          std::vector<QuantifierInfo *> new_qis;
          while(j < N) {
            auto qi = new QuantifierInfo();
            auto name = "!k" + std::to_string(_qc++);
            qi->quantifier = hcvc::Variable::create(name,
                                                    context().type_manager().int_type(),
                                                    *_context,
                                                    true);
            _quantifier_variables[predicate].insert(qi->quantifier);
            qi->accessor = hcvc::Variable::create("!" + parameter->name() + name,
                                                  dynamic_cast<const hcvc::ArrayType *>(parameter->type())->element_type(),
                                                  *_context,
                                                  true);
            _accessor_variables[predicate].insert(qi->accessor);
            qi->predicate = predicate;
            qi->array = parameter;
            qi->size_variable = parameter->size_variable();
            _quantifiers[predicate].push_back(qi);
            _array_quantifiers[predicate][parameter].push_back(qi);
            new_qis.push_back(qi);
            j++;
          }
        }
      }

      auto restrictions = _context->get_true();
      for(auto [array, quantifiers]: _array_quantifiers[predicate]) {
        for(unsigned long i = 0; i < quantifiers.size() - 1; i++) {
          auto qi1 = quantifiers[i];
          auto k1 = hcvc::VariableConstant::create(qi1->quantifier, 0, *_context);
          auto qi2 = quantifiers[i + 1];
          auto k2 = hcvc::VariableConstant::create(qi2->quantifier, 0, *_context);
          restrictions = restrictions && _context->apply("<=", {k1, k2});
        }
      }
      for(auto qi: _quantifiers[predicate]) {
        auto k = hcvc::VariableConstant::create(qi->quantifier, 0, *_context);
        _quantifier_exprs[predicate].push_back(k);
        auto T = hcvc::VariableConstant::create(qi->array, 0, *_context);
        auto Tk = hcvc::VariableConstant::create(qi->accessor, 0, *_context);
        _sub_maps[predicate][Tk] = _context->apply("[]", {T, k});
        auto size = hcvc::VariableConstant::create(qi->size_variable, 0, *_context);
        restrictions = restrictions &&
                       _context->apply("<=",
                                       {hcvc::IntegerLiteral::get("0", k->type(), *_context),
                                        k})
                       && _context->apply("<", {k, size});
      }
      _restrictions[predicate] = restrictions;
    }
  }

  hcvc::Expr QuantifierManager::quantify(const hcvc::Predicate *predicate, hcvc::Expr body, bool only_substitute) {
    if(predicate->may_require_quantifiers()) {
      auto constants = hcvc::get_constants(body);
      bool has_quantifier = false;
      for(const auto &constant_expr: constants) {
        auto constant = std::dynamic_pointer_cast<hcvc::Constant>(constant_expr);
        if(constant->is_variable_constant()) {
          auto var_constant = std::dynamic_pointer_cast<hcvc::VariableConstant>(constant);
          if(_quantifier_variables[predicate].count(var_constant->variable()) > 0
             || _accessor_variables[predicate].count(var_constant->variable()) > 0) {
            has_quantifier = true;
            break;
          }
        }
      }
      if(has_quantifier) {
        hcvc::Expr quant_inv;
        if(!only_substitute) {
          return hcvc::QuantifiedFormula::create(hcvc::Quantifier::ForAll,
                                                 _quantifier_exprs.at(predicate),
                                                 _context->apply("=>", {_restrictions.at(predicate),
                                                                        hcvc::substitute(body,
                                                                                         _sub_maps.at(predicate))}),
                                                 *_context);
        } else {
          return hcvc::substitute(body, _sub_maps.at(predicate));
        }
      }
    }
    return body;
  }
}
