#include "tapis/engines/hornice/qdt/diagram.hh"
#include "tapis/engines/hornice/qdt/aggregation.hh"
#include <stack>
#include <utility>
#include "hcvc/program/variable.hh"
#include "tapis/engines/options.hh"
#include "hcvc/logic/printer.hh"

namespace tapis::HornICE::qdt {

  //*-- Diagram
  Diagram::Diagram(const hcvc::Predicate *predicate, std::map<const hcvc::Variable *, hcvc::Expr> values,
                   std::string hash, z3::context &context)
      : _predicate(predicate),
        _values(std::move(values)),
        _hash(std::move(hash)),
        _constant(context.bool_const((std::string("!d!") + std::to_string(_dc++)).c_str())){}

  unsigned long Diagram::_dc = 0;

  //*-- DiagramManager
  DiagramManager::DiagramManager(tapis::HornICE::qdt::QuantifierManager &quantifier_manager,
                                 tapis::HornICE::qdt::AggregationManager &aggregation_manager,
                                 hcvc::Context &context)
      : _quantifier_manager(quantifier_manager),
        _aggregation_manager(aggregation_manager),
        _context(context) {}

const std::list<const Diagram *> &DiagramManager::get_diagrams(const hcvc::State *state) {
    std::set<const hcvc::Variable *> _skip_variables;
    for(auto var: state->predicate()->parameters()) {
        if(var->type()->is_array() && var->is_shadow()) {
            _skip_variables.insert(var);
        }
    }
    if(_state_diagrams.count(state) == 0) {
        bool has_array = false;
        for(auto &[var, _]: state->values()) {
            if(var->type()->is_array()) {
                has_array = true;
                break;
            }
        }
        if(has_array) {
            // This is the new, refactored combination generation logic 🚀
            std::list<std::map<const hcvc::Variable *, unsigned long>> combinations;
            
            // 1. Group QuantifierInfo objects by their underlying shared quantifier variable.
            std::map<const hcvc::Variable *, std::vector<QuantifierInfo*>> unique_quantifiers;
            std::map<QuantifierInfo *, unsigned long> max_sizes;

            for (auto qi : _quantifier_manager.quantifiers(state->predicate())) {
                if (_skip_variables.count(qi->array) > 0 && get_options().ice.qdt.abstract_summary_input_arrays) {
                    continue;
                }
                unique_quantifiers[qi->quantifier].push_back(qi);
                max_sizes[qi] = std::stol(
                    std::dynamic_pointer_cast<hcvc::IntegerLiteral>(state->values().at(qi->size_variable))->value());
            }

            // 2. Build combinations based on the unique quantifiers, not per-array.
            std::vector<const hcvc::Variable*> unique_quantifier_list;
            for(const auto& [quant_var, qi_list] : unique_quantifiers) {
                unique_quantifier_list.push_back(quant_var);
            }

            for (unsigned long i = 0; i < unique_quantifier_list.size(); ++i) {
                const auto* quant_var = unique_quantifier_list[i];
                const auto& qi_list = unique_quantifiers.at(quant_var);
                
                // All QIs for a shared quantifier should have the same max size. We take the first one.
                unsigned long max_val = max_sizes.at(qi_list[0]); 

                if (i == 0) {
                    for (unsigned long j = 0; j < max_val; ++j) {
                        combinations.emplace_back(std::map<const hcvc::Variable *, unsigned long>({{quant_var, j}}));
                    }
                } else {
                    const auto* prev_quant_var = unique_quantifier_list[i-1];
                    std::list<std::map<const hcvc::Variable *, unsigned long>> new_combinations;
                    for (const auto& old_comb : combinations) {
                        for (unsigned long k = 0; k < max_val; ++k) {
                            // This condition ensures ordered quantifiers (k_i <= k_{i+1})
                            if (old_comb.at(prev_quant_var) <= k) {
                                auto c = old_comb;
                                c[quant_var] = k;
                                new_combinations.push_back(c);
                            }
                        }
                    }
                    combinations = new_combinations;
                }
            }
            
            if (combinations.empty() && !unique_quantifier_list.empty()) {
                // This case can happen if max_size is 0 for the first quantifier.
                // We still need a single empty combination to proceed.
                combinations.push_back({});
            } else if (unique_quantifier_list.empty()) {
                // No quantifiers at all, create one diagram with no quantifier values.
                combinations.push_back({});
            }
            
            // 3. For each valid combination, create a diagram.
            for(auto &comb: combinations) {
                auto values = state->values();
                
                // For each unique quantifier in the combination, update all its associated QuantifierInfos
                for (const auto& [quant_var, value] : comb) {
                    const auto& qi_list = unique_quantifiers.at(quant_var);
                    for (const auto* qi : qi_list) {
                        values[qi->quantifier] = hcvc::IntegerLiteral::get(std::to_string(value), qi->quantifier->type(), _context);
                        values[qi->accessor] = std::dynamic_pointer_cast<hcvc::ArrayLiteral>(state->values().at(qi->array))->values().at(value);
                    }
                }
                
                // --- Aggregation logic remains the same ---
                const auto& agg_infos = _aggregation_manager.get_aggregations(state->predicate());
                for (const auto* info : agg_infos) {
                    if (values.find(info->array) == values.end()) { continue; }
                    auto array_literal = std::dynamic_pointer_cast<hcvc::ArrayLiteral>(values.at(info->array));
                    if (array_literal.get() == nullptr) { continue; }

                    long lower_val = 0;
                    if (info->lower_bound && values.count(info->lower_bound)) {
                        auto lit = std::dynamic_pointer_cast<hcvc::IntegerLiteral>(values.at(info->lower_bound));
                        if(lit) lower_val = std::stol(lit->value()); else continue;
                    } else if (info->lower_bound) { continue; }

                    long upper_val = 0;
                    if (info->upper_bound && values.count(info->upper_bound)) {
                        auto lit = std::dynamic_pointer_cast<hcvc::IntegerLiteral>(values.at(info->upper_bound));
                        if(lit) upper_val = std::stol(lit->value()); else continue;
                    } else { continue; }

                    long long current_sum = 0;
                    size_t array_size = array_literal->values().size();
                    if (lower_val <= upper_val && static_cast<size_t>(upper_val) <= array_size) {
                        for (long k = lower_val; k < upper_val; ++k) {
                            auto elem_lit = std::dynamic_pointer_cast<hcvc::IntegerLiteral>(array_literal->values().at(k));
                            if (elem_lit) current_sum += std::stoll(elem_lit->value());
                        }
                    }
                    values[info->variable] = hcvc::IntegerLiteral::get(std::to_string(current_sum), info->variable->type(), _context);
                }

                auto diagram = _get_diagram(state->predicate(), values);
                _state_diagrams[state].push_back(diagram);
            }
        } else {
            auto diagram = _get_diagram(state->predicate(), state->values());
            _state_diagrams[state].push_back(diagram);
        }
    }
    return _state_diagrams.at(state);
}
const Diagram *
DiagramManager::_get_diagram(const hcvc::Predicate *predicate,
                             const std::map<const hcvc::Variable *, hcvc::Expr> &values) {
    std::string hash = "(" + predicate->name();
    std::map<const hcvc::Variable *, hcvc::Expr> diagram_values;
    hcvc::Printer printer; // Use the printer for correct string conversion
    for(const auto &[k, v]: values) {
      if(!k->type()->is_array()) {
        hash += "," + k->name() + "=" + printer.to_string(v);
        diagram_values[k] = v;
      }
    }
    hash += ")";
    if(_diagrams.count(hash) == 0) {
      std::cout << "[Diagram Generated] " << hash << '\n';
      _diagrams[hash] = std::make_unique<Diagram>(predicate, diagram_values, hash, _z3_ctx);
    }
    return _diagrams.at(hash).get();

  }

  void DiagramManager::clear() {
    _diagrams.clear();
    _state_diagrams.clear();
  }

  //*-- DiagramImplication
  DiagramImplication::DiagramImplication(std::vector<const Diagram *> antecedents,
                                         const Diagram *consequent)
      : _antecedents(std::move(antecedents)),
        _consequent(consequent) {}

  //*-- DiagramPartialReachabilityGraph
  bool DiagramPartialReachabilityGraph::add_implication(const DiagramImplication *implication) {
    for(auto &antecedent: implication->antecedents()) {
      _add_diagram(antecedent);
      _out_impls[antecedent].insert(implication);
    }
    if(implication->consequent() != nullptr) {
      _add_diagram(implication->consequent());
      _in_impls[implication->consequent()].insert(implication);
    }
    if(!implication->antecedents().empty() && implication->consequent() != nullptr) {
      _implications.insert(implication);
    }
    if(_propagate_classification({implication}).first) {
      return true;
    }
    return false;
  }

  bool DiagramPartialReachabilityGraph::add_implication(const std::vector<const Diagram *> &antecedents,
                                                        const Diagram *consequent) {
    auto implication = new DiagramImplication(antecedents, consequent);
    return add_implication(implication);
  }

  bool
  DiagramPartialReachabilityGraph::horn_sat(const std::vector<const Diagram *> &diagrams, DiagramClass classification) {
    std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> target(_classifications);
    return std::get<0>(_general_horn_force(diagrams, classification, target));
  }

  DiagramHornForceResult
  DiagramPartialReachabilityGraph::horn_force(const std::vector<const Diagram *> &diagrams,
                                              DiagramClass classification) {
    return std::get<1>(_general_horn_force(diagrams, classification, _classifications));
  }

  void DiagramPartialReachabilityGraph::_add_diagram(const Diagram *state) {
    if(_classifications.count(state) == 0) {
      _classifications[state] = std::make_pair(DiagramClass::unknown, std::vector<const Diagram *>());
    }
  }

  DiagramClass _get_classification(const Diagram *diagram,
                                   const std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> &source) {
    if(source.count(diagram) > 0) {
      return source.at(diagram).first;
    }
    return DiagramClass::unknown;
  }

  bool _set_classification(const Diagram *diagram, DiagramClass classification,
                           const std::vector<const Diagram *> &affectors,
                           std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> &target) {
    if(target.count(diagram) > 0 && target[diagram].first != DiagramClass::unknown &&
       target[diagram].first != classification) {
      return false;
    }
    target[diagram] = std::make_pair(classification, affectors);
    return true;
  }

  bool _is_positive(const std::vector<const Diagram *> &antecedents,
                    const std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> &source) {
    return std::all_of(antecedents.begin(), antecedents.end(), [&](const Diagram *diagram) {
      return _get_classification(diagram, source) == DiagramClass::positive;
    });
  }

  bool _is_negative(const Diagram *consequent,
                    const std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> &source) {
    return consequent == nullptr || _get_classification(consequent, source) == DiagramClass::negative;
  }

  std::pair<bool, DiagramHornForceResult>
  DiagramPartialReachabilityGraph::_propagate_classification(
      const std::vector<const DiagramImplication *> &implications,
      std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> &target) {
    std::stack<const DiagramImplication *> working;
    std::list<const Diagram *> forced_pos;
    std::list<const Diagram *> forced_neg;
    for(auto implication: implications) {
      working.push(implication);
    }
    while(!working.empty()) {
      auto implication = working.top();
      working.pop();
      std::list<const DiagramImplication *> todo;
      const auto &antecedents = implication->antecedents();
      auto consequent = implication->consequent();
      if(_is_positive(antecedents, target)) {
        if(_is_negative(consequent, target)) {
          return std::make_pair(false, DiagramHornForceResult());
        }
        auto old_class = _get_classification(consequent, target);
        if(old_class != DiagramClass::positive) {
          _set_classification(consequent, DiagramClass::positive, implication->antecedents(), target);
          forced_pos.push_back(consequent);
          std::vector<std::set<const DiagramImplication *> *> sources{
              &_out_impls[consequent],
          };
          for(auto source: sources) {
            todo.insert(todo.end(), source->begin(), source->end());
          }
        }
      } else if(_is_negative(consequent, target)) {
        if(_is_positive(antecedents, target)) {
          return std::make_pair(false, DiagramHornForceResult());
        }
        std::vector<const Diagram *> unknowns;
        for(auto state: antecedents) {
          if(_get_classification(state, target) == DiagramClass::negative) {
            unknowns.clear();
            break;
          } else if(_get_classification(state, target) == DiagramClass::unknown) {
            unknowns.push_back(state);
          }
        }
        if(unknowns.size() == 1) {
          if(!implication->is_goal()) {
            std::vector<const Diagram *> others(antecedents);
            others.erase(std::remove(others.begin(), others.end(), unknowns[0]), others.end());
            others.push_back(consequent);
          }
          std::vector<const Diagram *> affectors;
          for(auto affector: affectors) {
            if(affector != unknowns[0]) {
              affectors.push_back(affector);
            }
          }
          if(consequent != nullptr && consequent != unknowns[0]) {
            affectors.push_back(consequent);
          }
          _set_classification(unknowns[0], DiagramClass::negative, affectors, target);
          forced_neg.push_back(unknowns[0]);
          std::vector<std::set<const DiagramImplication *> *> sources{
              &_in_impls[unknowns[0]],
          };
          for(auto source: sources) {
            todo.insert(todo.end(), source->begin(), source->end());
          }
        }
      }
      for(auto item: todo) {
        working.push(item);
      }
    }
    return std::make_pair(true, std::make_pair(forced_pos, forced_neg));
  }

  std::pair<bool, DiagramHornForceResult>
  DiagramPartialReachabilityGraph::_propagate_classification(
      const std::vector<const DiagramImplication *> &implications) {
    return _propagate_classification(implications, _classifications);
  }

  std::pair<bool, DiagramHornForceResult>
  DiagramPartialReachabilityGraph::_general_horn_force(const std::vector<const Diagram *> &diagrams,
                                                       DiagramClass classification,
                                                       std::unordered_map<const Diagram *, std::pair<DiagramClass, std::vector<const Diagram *>>> &target) {
    std::vector<const DiagramImplication *> implications;
    for(auto state: diagrams) {
      if(!_set_classification(state, classification, {}, target)) {
        return std::make_pair(false, DiagramHornForceResult());
      }
      std::vector<std::set<const DiagramImplication *> *> sources;
      if(classification == DiagramClass::positive) {
        sources.push_back(&_out_impls[state]);
      } else if(classification == DiagramClass::negative) {
        sources.push_back(&_in_impls[state]);
      }
      for(auto source: sources) {
        implications.insert(implications.end(), source->begin(), source->end());
      }
    }
    return _propagate_classification(implications, target);
  }

}