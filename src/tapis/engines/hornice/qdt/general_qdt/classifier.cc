//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "tapis/engines/hornice/qdt/general_qdt/classifier.hh"

#include <cassert>
#include <cmath>
#include <utility>
#include "rope.hh"
#include "tapis/engines/options.hh"
#include "tapis/engines/attributes/enumerator.hh"
#include "tapis/engines/hornice/qdt/hint_template.hh"
#include "tapis/engines/attributes/new_attr_synthesizer.hh"
#include <iomanip>

namespace tapis::HornICE::qdt::GeneralQDT {

std::string role_to_string(tapis::HornICE::qdt::VariableRole role) {
    switch (role) {
        case tapis::HornICE::qdt::VariableRole::UNKNOWN:    return "UNKNOWN";
        case tapis::HornICE::qdt::VariableRole::INDEX:      return "INDEX";
        case tapis::HornICE::qdt::VariableRole::QUANTIFIER: return "QUANTIFIER";
        case tapis::HornICE::qdt::VariableRole::ARRAY_SIZE: return "ARRAY_SIZE";
        case tapis::HornICE::qdt::VariableRole::ARRAY:      return "ARRAY";
        case tapis::HornICE::qdt::VariableRole::DATA:       return "DATA";
        case tapis::HornICE::qdt::VariableRole::LITERAL:    return "LITERAL";
        default:                                           return "INVALID_ROLE";
    }
}
  //*-- Classifier
  Classifier::Classifier(const hcvc::ClauseSet &clause_set,
                         std::set<const hcvc::Predicate *> predicates,
                         QuantifierManager &quantifier_manager,
                         AggregationManager &aggregation_manager)
      : qdt::Classifier(clause_set, std::move(predicates), quantifier_manager, aggregation_manager),
        _working_set(nullptr),
        _aggregation_manager(aggregation_manager) {  // Initialize the member
              
    _alpha = get_options().ice.qdt.hint_score_alpha;

    _attr_synthesizer = new NewAttributeSynthesizer(this->quantifier_manager(), _aggregation_manager);
    _attr_synthesizer->set_context(&this->quantifier_manager().context());
    _attr_synthesizer->set_predicate(this->predicates());
    _attr_synthesizer->set_manager(new AttributeManager());
    _attr_synthesizer->setup();
  }

  Classifier::~Classifier() {
    delete _working_set;
  }

  void Classifier::resetup_attributes() {
    delete _attr_synthesizer;
    _attr_synthesizer = new NewAttributeSynthesizer(this->quantifier_manager(), _aggregation_manager);
    _attr_synthesizer->set_context(&this->quantifier_manager().context());
    _attr_synthesizer->set_predicate(this->predicates());
    _attr_synthesizer->set_manager(new AttributeManager());
    _attr_synthesizer->setup();
  }

  class DTNode {
  public:
    explicit DTNode(hcvc::Context &context) : _context(context) {}

    const hcvc::Predicate *predicate;
    DiagramClass label = DiagramClass::unknown;
    const Attribute *attribute = nullptr;
    std::list<const Diagram *> pos;
    std::list<const Diagram *> neg;
    std::vector<const Diagram *> unclass;
    DTNode *left = nullptr;
    DTNode *right = nullptr;
    std::pair<std::list<const Attribute *>, std::list<const Attribute *>> attributes;
    hcvc::Context &_context;

    hcvc::Expr to_formula() {
      if(label == DiagramClass::positive) {
        return _context.get_true();
      } else if(label == DiagramClass::negative) {
        return _context.get_false();
      } else {
        return (attribute->constraint() && left->to_formula()) ||
               (!attribute->constraint() && right->to_formula());
      }
    }
  };

// Forward declarations
double NodeSimilarity(const std::shared_ptr<HintTemplate>& attr_template, const std::shared_ptr<HintTemplate>& hint_template);
void get_all_subtemplates(const std::shared_ptr<HintTemplate>& ht, std::vector<std::shared_ptr<HintTemplate>>& components);

// --- SCORING HELPERS ---

double get_op_weight(const hcvc::Operator* op) {
    if (!op) return 0.1; // For quantified formulas without a root op
    const auto& name = op->name();
    if (name == "sum" || name == "sum_range") return 10.0;
    if (name == "select" || name == "[]") return 8.0;
    if (name == "=") return 2.0;
    if (name == "<=" || name == "<" || name == ">=" || name == ">") return 1.0;
    if (name == "+" || name == "-") return 0.5;
    return 0.2; // Other operators
}

double OpSimilarity(const hcvc::Operator* op_a, const hcvc::Operator* op_b) {
    if (op_a == op_b) return 1.0;
    if (!op_a || !op_b) return 0.0;
    const auto& name_a = op_a->name();
    const auto& name_b = op_b->name();
    if (name_a == name_b) return 1.0;
    
    std::set<std::string> comparisons = {"<", "<=", "=", ">=", ">"};
    if (comparisons.count(name_a) && comparisons.count(name_b)) return 0.3; // Similarity for any two comparisons

    return 0.0;
}

int Complexity(const std::shared_ptr<HintTemplate>& ht) {
    if (!ht) return 1;
    int c = 1 + ht->simple_params.size();
    for (const auto& nested : ht->nested_params) { c += Complexity(nested); }
    return c;
}

void get_all_subtemplates(const std::shared_ptr<HintTemplate>& ht, std::vector<std::shared_ptr<HintTemplate>>& components, const std::string& label) {
    if (!ht) return;
    components.push_back(ht);
    // std::cerr << "    [" << label << " Subtree] Found component: " << (ht->op ? ht->op->name() : "[Quant/Leaf]") << "\n";
    for (const auto& nested : ht->nested_params) {
        get_all_subtemplates(nested, components, label);
    }
}
double ParamSimilarity(const TemplateParameter& attr_param, const TemplateParameter& hint_param) {
    // 📣 Initial debug print for the comparison
    // std::cerr << "        [ParamSim] Comparing '" << attr_param.expr << "' (Role: " << role_to_string(attr_param.role) 
    //           << ") vs '" << hint_param.expr << "' (Role: " << role_to_string(hint_param.role) << ")\n";

    // // A fast path for identical expressions
    // if (attr_param.expr == hint_param.expr) {
    //     std::cerr << "        [ParamSim] -> Result: 1.0 (Exact Expr Match)\n";
    //     return 1.0;
    // }

    // Case 1: Both parameters are variables
    if (is_var_cnst(attr_param.expr) && is_var_cnst(hint_param.expr)) {
auto attr_v = std::dynamic_pointer_cast<hcvc::VariableConstant>(attr_param.expr)->variable();
        auto hint_v = std::dynamic_pointer_cast<hcvc::VariableConstant>(hint_param.expr)->variable();
        
        // This is a more robust check for pointer equality on the underlying variable
        if (attr_v == hint_v) {
            // std::cerr << "        [ParamSim] -> Result: 1.0 (Identical Variable)\n";
            return 1.0;
        }

        VariableRole attr_role = attr_param.role;
        VariableRole hint_role = hint_param.role;

        if (attr_role == VariableRole::QUANTIFIER && hint_role == VariableRole::QUANTIFIER) {
            // std::cerr << "        [ParamSim] -> Result: 1.0 (Quantifier Role Match)\n";
            return 1.0;
        }
        if (attr_v->name() == hint_v->name()) {
            // std::cerr << "        [ParamSim] -> Result: 1.0 (Name Match)\n";
            return 1.0;
        }
        if (attr_role == VariableRole::ARRAY || hint_role == VariableRole::ARRAY) {
            // std::cerr << "        [ParamSim] -> Result: 0.0 (Array Mismatch)\n";
            return 0.0;
        }
        if ((attr_role == VariableRole::DATA && hint_role != VariableRole::DATA) ||
            (hint_role == VariableRole::DATA && attr_role != VariableRole::DATA)) {
            // std::cerr << "        [ParamSim] -> Result: 0.0 (Data/Non-Data Mismatch)\n";
            return 0.0;
        }
        if (attr_role == hint_role) {
            double score = (attr_role == VariableRole::INDEX) ? 0.8 : 0.6;
            // std::cerr << "        [ParamSim] -> Result: " << score << " (Role Match)\n";
            return score;
        }
        if ((attr_role == VariableRole::QUANTIFIER && hint_role == VariableRole::INDEX) ||
            (attr_role == VariableRole::INDEX && hint_role == VariableRole::QUANTIFIER)) {
            // std::cerr << "        [ParamSim] -> Result: 0.7 (Quantifier/Index Match)\n";
            return 0.7;
        }
    }

    // Case 2: Both parameters are literals
    if (attr_param.role == VariableRole::LITERAL && hint_param.role == VariableRole::LITERAL) {
        if (hcvc::to_string(attr_param.expr) == hcvc::to_string(hint_param.expr)) {
            // std::cerr << "        [ParamSim] -> Result: 1.0 (Literal Value Match)\n";
            return 1.0;
        }
    }
    
    // All other combinations are mismatches
    // std::cerr << "        [ParamSim] -> Result: 0.0 (Mismatch)\n";
    return 0.0;
}

double NodeSimilarity(const std::shared_ptr<HintTemplate>& attr_template, const std::shared_ptr<HintTemplate>& hint_template) {
    static int depth = 0; // For indented printing
    std::string indent(depth * 2, ' ');

    if (!attr_template || !hint_template) return 0.0;
    
    // Print the nodes being compared
    // std::cerr << indent << "[NodeSim] Comparing: " 
              // << (attr_template->op ? attr_template->op->name() : "Leaf") << " vs " 
              // << (hint_template->op ? hint_template->op->name() : "Leaf") << "\n";

    double op_sim = OpSimilarity(attr_template->op, hint_template->op);
    if (op_sim == 0.0) {
        // std::cerr << indent << "[NodeSim] -> FAIL: Operator Mismatch\n";
        return 0.0;
    }
    // Strict arity check (can be relaxed if needed)
    if (attr_template->simple_params.size() != hint_template->simple_params.size() ||
        attr_template->nested_params.size() != hint_template->nested_params.size()) {
        // std::cerr << indent << "[NodeSim] -> FAIL: Arity Mismatch\n";
        return 0.0;
    }

    depth++;
    double op_weight = get_op_weight(attr_template->op);
    double weighted_score_sum = op_sim * op_weight;
    double total_complexity = op_weight;

    for (size_t i = 0; i < attr_template->simple_params.size(); ++i) {
        weighted_score_sum += ParamSimilarity(attr_template->simple_params[i], hint_template->simple_params[i]);
        total_complexity += 1;
    }
    for (size_t i = 0; i < attr_template->nested_params.size(); ++i) {
        int child_comp = Complexity(hint_template->nested_params[i]);
        weighted_score_sum += NodeSimilarity(attr_template->nested_params[i], hint_template->nested_params[i]) * child_comp;
        total_complexity += child_comp;
    }
    depth--;
    
    double result_score = (total_complexity > 0) ? (weighted_score_sum / total_complexity) : 0.0;
    // std::cerr << indent << "[NodeSim] -> SUCCESS: Score = " << result_score << "\n";
    return result_score;
}


// double CalculateHintScore(const std::shared_ptr<HintTemplate>& attr_template, const std::shared_ptr<HintTemplate>& hint_template) {
//     if (!attr_template || !hint_template) return 0.0;

//     std::vector<std::shared_ptr<HintTemplate>> attr_concepts;
//     get_all_subtemplates(attr_template, attr_concepts);

//     std::vector<std::shared_ptr<HintTemplate>> hint_concepts;
//     get_all_subtemplates(hint_template, hint_concepts);
    
//     std::cerr << "    [HintScore] Attr Concepts: " << attr_concepts.size() << ", Hint Concepts: " << hint_concepts.size() << "\n";
//     if (attr_concepts.empty() || hint_concepts.empty()) return 0.0;

//     double total_weighted_score = 0.0;
//     double total_weight = 0.0;

//     for (const auto& attr_concept : attr_concepts) {
//         double best_match_for_this_concept = 0.0;
//         for (const auto& hint_concept : hint_concepts) {
//             best_match_for_this_concept = std::max(best_match_for_this_concept, NodeSimilarity(attr_concept, hint_concept));
//         }
        
//         double weight = get_op_weight(attr_concept->op);
//         total_weighted_score += best_match_for_this_concept * weight;
//         total_weight += weight;
//         std::cerr << "    [HintScore]   -> Best match for Attr component '" << (attr_concept->op ? attr_concept->op->name() : "Quant") 
//                   << "' was " << best_match_for_this_concept << " (Weight: " << weight << ")\n";
//     }

//     double final_score = (total_weight > 0) ? (total_weighted_score / total_weight) : 0.0;
//     std::cerr << "    [HintScore] -> Final Weighted Score: " << final_score << "\n";
//     return final_score;
// }

void get_all_variables_from_template(const std::shared_ptr<HintTemplate>& ht, std::set<const hcvc::Variable*>& vars) {
    if (!ht) return;
    for (const auto& param : ht->simple_params) {
        if (is_var_cnst(param.expr)) {
            vars.insert(std::dynamic_pointer_cast<hcvc::VariableConstant>(param.expr)->variable());
        }
    }
    for (const auto& nested : ht->nested_params) {
        get_all_variables_from_template(nested, vars);
    }
}

double CalculateStructuralSimilarity(const std::shared_ptr<HintTemplate>& attr_template, const std::shared_ptr<HintTemplate>& hint_template) {
    if (!attr_template || !hint_template) return 0.0;

    std::vector<std::shared_ptr<HintTemplate>> attr_concepts;
    get_all_subtemplates(attr_template, attr_concepts, "Attr");

    std::vector<std::shared_ptr<HintTemplate>> hint_concepts;
    get_all_subtemplates(hint_template, hint_concepts, "Hint");
    
    if (attr_concepts.empty() || hint_concepts.empty()) return 0.0;

    // std::cerr << "    [StructSim] --- Calculating Structural Similarity ---\n";
    double total_weighted_score = 0.0;
    double total_weight = 0.0;

    for (const auto& attr_concept : attr_concepts) {
        double best_match_for_this_concept = 0.0;
        for (const auto& hint_concept : hint_concepts) {
            best_match_for_this_concept = std::max(best_match_for_this_concept, NodeSimilarity(attr_concept, hint_concept));
        }
        
        double weight = get_op_weight(attr_concept->op);
        total_weighted_score += best_match_for_this_concept * weight;
        total_weight += weight;

        // 📣 This print shows the score for each component of the attribute.
        // std::cerr << "    [StructSim]   -> Best match for Attr component '" 
        //           << (attr_concept->op ? attr_concept->op->name() : "Leaf") 
        //           << "' was " << std::fixed << std::setprecision(3) << best_match_for_this_concept 
        //           << " (Weight: " << weight << ")\n";
    }

    double final_score = (total_weight > 0) ? (total_weighted_score / total_weight) : 0.0;
    // std::cerr << "    [StructSim] --- Final Structural Score: " << final_score << " ---\n";
    return final_score;
}
const std::shared_ptr<HintTemplate>& find_core_hint(const std::shared_ptr<HintTemplate>& ht) {
    if (!ht || ht->nested_params.empty()) {
        return ht;
    }
    // Heuristic: if op is null, it's a QuantifiedFormula, so get its body.
    // If it's an implication (=>), get the right-hand side.
    if (!ht->op || ht->op->name() == "=>") {
        return find_core_hint(ht->nested_params.back());
    }
    return ht;
}


double CalculateHintScore(const std::shared_ptr<HintTemplate>& attr_template, const std::shared_ptr<HintTemplate>& hint_template) {
    if (!attr_template || !hint_template) return 0.0;

    // // --- High-level context ---
    // std::cerr << "\n  [HintScore] <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n";
    // std::cerr << "  [HintScore] Comparing Attribute Template:\n";
    // print_hint_template(attr_template, 4);
    // std::cerr << "  [HintScore] Against Hint Template:\n";
    // print_hint_template(hint_template, 4);
    // std::cerr << "  [HintScore] --------------------------------------------------------\n";

// 1. Calculate the flexible, component-based Structural Similarity
    double structural_score = CalculateStructuralSimilarity(attr_template, hint_template);
    // std::cerr << "    [HintScore] -> Component Score (Flexible): " << std::fixed << std::setprecision(3) << structural_score << "\n";

    // 2. Calculate Structurally-Aware Variable Overlap Score
    
    // 2a. Get the core logical part of the hint
    const auto& core_hint = find_core_hint(hint_template);
    
    // 2b. Calculate a strict, top-down similarity score
    double top_down_sim = NodeSimilarity(attr_template, core_hint);
    // std::cerr << "    [HintScore] -> Top-Down Struct Match: " << std::fixed << std::setprecision(3) << top_down_sim << "\n";

    // 2c. Calculate the variable Jaccard index
    std::set<const hcvc::Variable*> attr_vars;
    get_all_variables_from_template(attr_template, attr_vars);
    std::set<const hcvc::Variable*> hint_vars;
    get_all_variables_from_template(hint_template, hint_vars);
    
    std::set<const hcvc::Variable*> intersection;
    std::set_intersection(attr_vars.begin(), attr_vars.end(), hint_vars.begin(), hint_vars.end(),
                          std::inserter(intersection, intersection.begin()));
    std::set<const hcvc::Variable*> union_set = attr_vars;
    union_set.insert(hint_vars.begin(), hint_vars.end());
    double jaccard_score = union_set.empty() ? 1.0 : static_cast<double>(intersection.size()) / union_set.size();
    // std::cerr << "    [HintScore] -> Variable Jaccard Index: " << jaccard_score << "\n";

    // 2d. The new score is the product of the two
    double variable_overlap_score = top_down_sim * jaccard_score;
    // std::cerr << "    [HintScore] -> Structurally-Aware Overlap: " << variable_overlap_score << "\n";

    // 3. Combine the flexible structural score and the strict overlap score
    const double beta = 0.5; // 80% weight to flexible structure, 20% to strict overlap
    double final_score = (beta * structural_score) + ((1 - beta) * variable_overlap_score);

    // std::cerr << "    [HintScore] ===> Final Blended Score: " << std::fixed << std::setprecision(3) << final_score << "\n";
    return final_score;
}


  std::optional<std::unordered_map<const hcvc::Predicate *, hcvc::Expr>>
  Classifier::classify(const tapis::HornICE::qdt::DiagramPartialReachabilityGraph &diag_set) {
    // std::cout << "inside Classifier::classify\n";
    delete _working_set;
    _working_set = new DiagramPartialReachabilityGraph(diag_set);

    // check if attributes are sufficient for classification and generate more otherwise
    while(!are_attributes_sufficient()) {
      delete _working_set;
      _working_set = new DiagramPartialReachabilityGraph(diag_set);
      std::cout << "Attributes are not sufficient, generating more...\n";
      if(!_attr_synthesizer->generate_attributes(_working_set)) {
        return std::nullopt;
      }
      std::cout << "I am here \n";

    }

    // Pre-processing loop to translate and cache templates for all attributes.
  std::cerr << "[DEBUG] Pre-processing attributes to create cached templates...\n";
  ExprToTemplateConverter converter;
  for (auto predicate : this->predicates()) {
      auto attribute_sets = _attr_synthesizer->attributes(predicate);
      for (auto* attr : rope::add(attribute_sets.first, attribute_sets.second)) {
          // 1. Get the attribute's constraint (in diagram/synthetic language)
          auto synthetic_expr = attr->constraint();

          // 2. "Lift" it to SMT-LIB language using the manager's substitution maps.
          auto lifted_expr_agg = _aggregation_manager.substitute(predicate, synthetic_expr);
          auto lifted_expr_final = quantifier_manager().quantify(predicate, lifted_expr_agg, true);

          // 3. Convert the SMT-LIB form into a HintTemplate
          auto ht = converter.convert(lifted_expr_final);

          // 4. Cache the result inside the attribute object
          const_cast<Attribute*>(attr)->set_cached_template(ht);
      }
  }
  std::cerr << "[DEBUG] Attribute pre-processing complete.\n";

    // create a root tree for each predicate and prepare data
    std::map<const hcvc::Predicate *, DTNode *> roots;
    for(auto predicate: this->predicates()) {
      roots[predicate] = new DTNode(this->quantifier_manager().context());
      roots[predicate]->predicate = predicate;
      auto attributes = _attr_synthesizer->attributes(predicate);
      roots[predicate]->attributes = std::make_pair(
          std::list<const Attribute *>(attributes.first.begin(),
                                       attributes.first.end()),
          std::list<const Attribute *>(attributes.second.begin(),
                                       attributes.second.end()));
    }
    for(const auto &[diagram, p]: _working_set->classifications()) {
      if(p.first == DiagramClass::positive) {
        roots[diagram->predicate()]->pos.push_back(diagram);
      } else if(p.first == DiagramClass::negative) {
        roots[diagram->predicate()]->neg.push_back(diagram);
      } else {
        roots[diagram->predicate()]->unclass.push_back(diagram);
      }
    }

    // put the root to the working stack
    std::vector<DTNode *> leaves;
    for(auto [_, root]: roots) {
      leaves.push_back(root);
    }
    std::cout << " Learn the trees " << leaves.size() << "\n";

    // learn the trees
    while(!leaves.empty()) {
      for(unsigned long i = 0; i < leaves.size(); i++) {
        auto leaf = leaves[i];
        for(unsigned long j = 0; j < leaf->unclass.size(); j++) {
          auto diagram = leaf->unclass[j];
          if(_working_set->get_classification(diagram) == DiagramClass::positive) {
            leaf->pos.push_back(diagram);
            leaf->unclass.erase(leaf->unclass.begin() + j);
            j--;
          } else if(_working_set->get_classification(diagram) == DiagramClass::negative) {
            leaf->neg.push_back(diagram);
            leaf->unclass.erase(leaf->unclass.begin() + j);
            j--;
          }
        }

        if(leaf->unclass.empty()) {
          if(leaf->neg.empty()) {
            leaf->label = DiagramClass::positive;
            leaves.erase(leaves.begin() + i);
            i--;
            continue;
          } else if(leaf->pos.empty()) {
            leaf->label = DiagramClass::negative;
            leaves.erase(leaves.begin() + i);
            i--;
            continue;
          }
        }

        if(leaf->neg.empty()) {
          if(_working_set->horn_sat(leaf->unclass, DiagramClass::positive)) {
            _working_set->horn_force(leaf->unclass, DiagramClass::positive);
          }
        }
        if(leaf->pos.empty()) {
          if(_working_set->horn_sat(leaf->unclass, DiagramClass::negative)) {
            _working_set->horn_force(leaf->unclass, DiagramClass::negative);
          }
        }
        if(true) {
          auto& hints_for_pred = _attr_synthesizer->get_hint_templates(leaf->predicate);
                const Attribute *attribute = nullptr;
                double best_total_score = -1.0;

                if(!leaf->attributes.first.empty()) {
                    attribute = *leaf->attributes.first.begin();
                } else if (!leaf->attributes.second.empty()) {
                    attribute = *leaf->attributes.second.begin();
                }

                for(auto attr: rope::add(leaf->attributes.first, leaf->attributes.second)) {
                    double ig = gain(attr, leaf->pos, leaf->neg, leaf->unclass);
                    const auto& attr_template = attr->get_cached_template();
                    double hint_score = 0.0;

                    if (attr_template && !hints_for_pred.empty()) {
                        // std::cerr << "\n[DEBUG] >>> Scoring Attr: " << attr->constraint() << "\n";
                        for (const auto& hint_template : hints_for_pred) {
                            hint_score = std::max(hint_score, CalculateHintScore(attr_template, hint_template));
                        }
                    }
                    
                    double total_score = (_alpha * ig) + ((1 - _alpha) * hint_score);

                    
                    // std::cerr << "[SCORE] Attr: " << std::left << std::setw(35) << attr->constraint()
                    //           << " | Gain: " << std::fixed << std::setprecision(3) << ig 
                    //           << " | HintScore: " << hint_score
                    //           << " | Total: " << total_score << "\n";

                    if(total_score > best_total_score) {
                        best_total_score = total_score;
                        attribute = attr;
                        // Early exit for a perfect score (max info gain AND max hint score)
                        if (ig >= 1.0 && hint_score >= 1.0) {
                            break;
                        }
                    }
                }


          if(attribute == nullptr) {
            leaf->label = DiagramClass::negative;
            if(_working_set->horn_sat(leaf->unclass, DiagramClass::negative)) {
              _working_set->horn_force(leaf->unclass, DiagramClass::negative);
            }
            continue;
          }

          leaf->attributes.first.remove(attribute);
          leaf->attributes.second.remove(attribute);

          auto L = new DTNode(leaf->_context);
          auto R = new DTNode(leaf->_context);
          L->predicate = leaf->predicate;
          R->predicate = leaf->predicate;
          leaf->attribute = attribute;
          leaf->left = L;
          leaf->right = R;
          L->attributes = leaf->attributes;
          R->attributes = leaf->attributes;
          std::list<const hcvc::State *> sat_pos, sat_neg, sat_unclass;
          std::list<const hcvc::State *> unsat_pos, unsat_neg, unsat_unclass;
          for(auto diagram: leaf->pos) {
            if(attribute->satisfied_by(diagram)) {
              L->pos.push_back(diagram);
            } else {
              R->pos.push_back(diagram);
            }
          }
          for(auto diagram: leaf->neg) {
            if(attribute->satisfied_by(diagram)) {
              L->neg.push_back(diagram);
            } else {
              R->neg.push_back(diagram);
            }
          }
          for(auto diagram: leaf->unclass) {
            if(attribute->satisfied_by(diagram)) {
              L->unclass.push_back(diagram);
            } else {
              R->unclass.push_back(diagram);
            }
          }

          leaves.erase(leaves.begin() + i);
          leaves.push_back(L);
          leaves.push_back(R);
          i--;
        }
      }
    }

    std::unordered_map<const hcvc::Predicate *, hcvc::Expr> solution;
#ifndef NDEBUG
    std::cout << "Classifier.learn!" << "\n";
#endif
    for(auto [predicate, leaf]: roots) {
      solution.emplace(predicate, leaf->to_formula());
#ifndef NDEBUG
      std::cout << "    -" << predicate->name() << ": " << solution.at(predicate) << "\n";
#endif
    }
    return solution;
  }

  bool Classifier::are_attributes_sufficient() {
    for(auto predicate: this->predicates()) {
      std::map<std::vector<bool>, std::vector<const Diagram *>> eq_classes;
      auto attributes = _attr_synthesizer->attributes(predicate);
      for(auto &[diagram, _]: _working_set->classifications()) {
        if(diagram->predicate() == predicate) {
          std::vector<bool> eq_class;
          eq_class.reserve(attributes.first.size() + attributes.second.size());
          for(auto attr: rope::add(attributes.first, attributes.second)) {
            if(attr->satisfied_by(diagram)) {
              eq_class.push_back(true);
            } else {
              eq_class.push_back(false);
            }
          }
          eq_classes[eq_class].push_back(diagram);
        }
      }

      for(auto &[key, value]: eq_classes) {
        auto classification = DiagramClass::unknown;
        for(auto diagram: value) {
          auto sc = _working_set->get_classification(diagram);
          if(classification != DiagramClass::unknown && sc != DiagramClass::unknown && classification != sc) {
#ifndef NDEBUG
            for(auto &diagram1: value) {
              std::cout << diagram1->hash() << " - " << (int) _working_set->get_classification(diagram1) << "\n";
            }
#endif
            return false;
          }
          if(sc != DiagramClass::unknown) {
            classification = sc;
          }
        }
        if(classification != DiagramClass::unknown) {
          if(_working_set->horn_sat(value, classification)) {
            _working_set->horn_force(value, classification);
          } else {
            return false;
          }
        }
        if(value.size() >= 2) {
          for(unsigned long i = 0; i < value.size() - 1; i++) {
            for(unsigned long j = i + 1; j < value.size(); j++) {
              _working_set->add_implication({value[i]}, value[j]);
              _working_set->add_implication({value[j]}, value[i]);
            }
          }
        }
      }
    }
    return true;
  }

  double Classifier::gain(const tapis::HornICE::qdt::Attribute *attribute, const std::list<const Diagram *> &pos,
                          const std::list<const Diagram *> &neg, const std::vector<const Diagram *> &unclass) {
    // compute entropy
    double all_pos = 0;
    double all_neg = 0;
    double sat_pos = 0;
    double sat_neg = 0;
    double sat_unclass = 0;
    double unsat_pos = 0;
    double unsat_neg = 0;
    double unsat_unclass = 0;
    for(auto diagram: pos) {
      if(attribute->satisfied_by(diagram)) {
        sat_pos += 1;
      } else {
        unsat_pos += 1;
      }
      all_pos += 1;
    }
    for(auto diagram: neg) {
      if(attribute->satisfied_by(diagram)) {
        sat_neg += 1;
      } else {
        unsat_neg += 1;
      }
      all_neg += 1;
    }
    for(auto diagram: unclass) {
      if(attribute->satisfied_by(diagram)) {
        sat_unclass += 1;
      } else {
        unsat_unclass += 1;
      }
      all_neg += 1;
    }
    if((sat_pos == 0 && sat_neg == 0 && sat_unclass == 0) ||
       (unsat_pos == 0 && unsat_neg == 0 && unsat_unclass == 0)) {
      return 0;
    }
    // all entropy
    double all_H;
    if(all_pos == 0 || all_neg == 0) {
      all_H = 0;
    } else {
      auto np = all_pos + all_neg;
      auto pnp = all_pos / np;
      auto nnp = all_neg / np;
      all_H = -std::log2(pnp) * pnp - std::log2(nnp) * nnp;
    }
    // sat entropy
    double sat_H;
    if(sat_pos == 0 || sat_neg == 0) {
      sat_H = 0;
    } else {
      auto np = sat_pos + sat_neg;
      auto pnp = sat_pos / np;
      auto nnp = sat_neg / np;
      sat_H = -std::log2(pnp) * pnp - std::log2(nnp) * nnp;
    }
    // unsat entropy
    double unsat_H;
    if(unsat_pos == 0 || unsat_neg == 0) {
      unsat_H = 0;
    } else {
      auto np = unsat_pos + unsat_neg;
      auto pnp = unsat_pos / np;
      auto nnp = unsat_neg / np;
      unsat_H = -std::log2(pnp) * pnp - std::log2(nnp) * nnp;
    }
    // information gain
    double ig = all_H - (sat_pos + sat_neg) / (all_pos + all_neg) * sat_H -
                (unsat_pos + unsat_neg) / (all_pos + all_neg) * unsat_H;
    return ig;
  }

}
