//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include <filesystem>
#include <iostream>
#include <string>
#include "apronxx/apxx_box.hh"
#include "apronxx/apxx_oct.hh"
#include "apronxx/apxx_polka.hh"
#include "hcvc/utils/source.hh"
#include "tapis/engines/engine.hh"
#include "tapis/engines/horn_ice_qdt.hh"
#include "tapis/engines/options.hh"
#include "tapis/engines/outputs.hh"
#include "tapis/engines/ai/ai.hh"
#include "hcvc/fe/c/cfrontend.hh"
#include "hcvc/utils/to_smtlib.hh"

tapis::AttributeDomain string_to_enum_domain(const std::string &input) {
  if(input == "emp") {
    return tapis::AttributeDomain::Empty;
  } else if(input == "eq") {
    return tapis::AttributeDomain::Equality;
  } else if(input == "ub") {
    return tapis::AttributeDomain::UpperBound;
  } else if(input == "sub") {
    return tapis::AttributeDomain::StrictUpperBound;
  } else if(input == "int") {
    return tapis::AttributeDomain::Interval;
  } else if(input == "db") {
    return tapis::AttributeDomain::DifferenceBound;
  } else if(input == "oct") {
    return tapis::AttributeDomain::Octagon;
  } else if(input == "octh") {
    return tapis::AttributeDomain::Octahedron;
  } else if(input == "poly") {
    return tapis::AttributeDomain::Polyhedra;
  } else if(input == "kmod0") {
    return tapis::AttributeDomain::Kmod0;
  }
  // TODO: throw an error for unknown domain
  exit(10);
}

std::set<tapis::AttributeDomain> string_to_enum_domains(std::string input) {
  std::string delimiter = "+";
  std::set<tapis::AttributeDomain> res;
  unsigned long pos;
  std::string token;
  while((pos = input.find(delimiter)) != std::string::npos) {
    token = input.substr(0, pos);
    res.insert(string_to_enum_domain(token));
    input.erase(0, pos + delimiter.length());
  }
  res.insert(string_to_enum_domain(input));
  return res;
}

std::set<std::string> split_string_to_set(std::string input, const std::string& delimiter) {
    std::set<std::string> result;
    size_t pos = 0;
    std::string token;
    while ((pos = input.find(delimiter)) != std::string::npos) {
        token = input.substr(0, pos);
        if (!token.empty()) {
            result.insert(token);
        }
        input.erase(0, pos + delimiter.length());
    }
    if (!input.empty()) {
        result.insert(input);
    }
    return result;
}

int main(int argc, char *argv[]) {
  //*- parse options
  tapis::Options &options = tapis::get_options();
  for(int i = 1; i < argc; i++) {
    std::string argument(argv[i]);
    if(!argument.compare(0, 2 /* "==".size() */, "--")) {
      if(argument == "--print-invs") {
        options.print_invs = true;
      }
      // absint options
      else if(argument == "--no-absint.perform") {
        options.absint.perform = false;
      } else if(argument == "--absint-domain") {
        tapis::AbsIntDomain domain;
        std::string domain_str(argv[i + 1]);
        i++;
        if(domain_str == "box") {
          domain = tapis::AbsIntDomain::Box;
        } else if(domain_str == "oct") {
          domain = tapis::AbsIntDomain::Octagon;
        } else if(domain_str == "polka") {
          domain = tapis::AbsIntDomain::Polka;
        } else {
          // TODO: throw an error for unknown absint domain
          return 10;
        }
        options.absint.domain = domain;
      }
        // engine
      else if(argument == "--engine") {
        tapis::EngineKind engine;
        std::string engine_str(argv[i + 1]);
        i++;
        if(engine_str == "qdt") {
          engine = tapis::EngineKind::horn_ice_qdt;
        } else if(engine_str == "c2smt2") {
          engine = tapis::EngineKind::c_to_smtlib;
        } else {
          // TODO: throw an error for unknown engine
          return 10;
        }
        options.engine = engine;
      }
        // ice options
      else if(argument == "--ice.teacher.multiple_cex") {
        options.ice.teacher.multiple_counterexamples = true;
      }
        // enumeration options
      else if(argument == "--ice.learner.enumerator.domains") {
        std::string domains_str(argv[i + 1]);
        i++;
        auto domains = string_to_enum_domains(domains_str);
        options.ice.learner.index_domains = domains;
        options.ice.learner.data_domains = domains;
      } else if(argument == "--ice.learner.index_domains") {
        std::string domains_str(argv[i + 1]);
        i++;
        auto domains = string_to_enum_domains(domains_str);
        options.ice.learner.index_domains = domains;
      } else if(argument == "--ice.learner.data_domains") {
        std::string domains_str(argv[i + 1]);
        i++;
        auto domains = string_to_enum_domains(domains_str);
        options.ice.learner.data_domains = domains;
      } else if(argument == "--no-ice.learner.attr_from_spec") {
        options.ice.learner.attr_from_spec = false;
      } else if(argument == "--no-ice.learner.attr_from_program") {
        options.ice.learner.attr_from_program = false;
      } else if(argument == "--ice.learner.mix_data_indexes") {
        options.ice.learner.mix_data_indexes = true;
      }
        // qdt options
      else if(argument == "--qdt.quantifiers") {
        std::string quantifiers_str(argv[i + 1]);
        i++;
        options.ice.qdt.quantifier_numbers = std::stol(quantifiers_str);
      } else if(argument == "--qdt.share-quantifiers") {
        std::string arrays_str(argv[i + 1]);
        i++;
        auto shared_group = split_string_to_set(arrays_str, ",");
        if (!shared_group.empty()) {
            options.ice.qdt.shared_quantifier_groups.push_back(shared_group);
        }
      }else if(argument == "--qdt.use-sum-on-arrays") {
        std::string arrays_str(argv[i + 1]);
        i++;
        options.ice.qdt.use_sum_on_arrays = split_string_to_set(arrays_str, ",");
      }
      else if(argument == "--no-qdt.bounded_data_values") {
        options.ice.qdt.bounded_data_values = false;
      } else if(argument == "--qdt.eq_classes_attr_vars") {
        options.ice.qdt.eq_classes_attr_vars = true;
      } else if(argument == "--no-qdt.abstract-summary-input-arrays") {
        options.ice.qdt.abstract_summary_input_arrays = false;
      } else if(argument == "--qdt.quantification") {
        std::string quantification(argv[i + 1]);
        i++;
        for(auto c: quantification) {
          if(c == 'f') {
            options.ice.qdt.quantification.push_back(hcvc::Quantifier::ForAll);
          } else if(c == 'e') {
            options.ice.qdt.quantification.push_back(hcvc::Quantifier::Exists);
          } else {
            std::cout << "Unknown quantification type" << "\n";
            exit(12);
          }
        }
      }
      else if(argument == "--qdt.alpha") {
        std::string alpha_str(argv[i + 1]);
        i++;
        try {
            double alpha_val = std::stod(alpha_str);
            if (alpha_val >= 0.0 && alpha_val <= 1.0) {
                options.ice.qdt.hint_score_alpha = alpha_val;
            } else {
                std::cerr << "Error: --qdt.alpha value must be between 0.0 and 1.0." << std::endl;
                return 1; // Exit with an error code
            }
        } catch (const std::invalid_argument& e) {
            std::cerr << "Error: Invalid number for --qdt.alpha: " << alpha_str << std::endl;
            return 1;
        }
      }
        // output options
      else if(argument == "--stats") {
        options.output.statistics = true;
      } else {
        // TODO: throw an error for unknown argument
        return 10;
      }
      continue;
    }
    options.path = argument;
  }

  tapis::Outputs &outputs = tapis::get_outputs();

  //*- parse the input C file and compile it to hcvc's verification conditions
  if(!std::filesystem::exists(options.path)) {
    std::cout << "UNSAFE - File doesn't exists\n";
    return 0;
  }
  hcvc::FileSource file(options.path);
  hcvc::fe::CFrontend cfe;
  auto module = cfe.process(file);
  std::set<hcvc::Weakness> weaknesses = {
      hcvc::Weakness::assertion_violation,
      hcvc::Weakness::specification_violation
  };
  auto clauses = module->hypergraph().get_clauses(weaknesses);
  outputs.clauses = clauses;
#ifndef NDEBUG
  for(auto clause: clauses.to_set()) {
    clause->dump();
  }
#endif

  //*- perform an abstract interpretation pre-analysis if demanded
  std::map<const hcvc::Predicate *, hcvc::Expr> absint_fixpoint;
  for(auto predicate: module->hypergraph().get_clauses(weaknesses).predicates()) {
    outputs.preanalysis_invariants[predicate] = module->context().get_true();
  }

  if(options.absint.perform) {
    tapis::ai::AbstractInterpreter abstract_interpreter(module, weaknesses);
    apron::manager *apron_manager;
    if(options.absint.domain == tapis::AbsIntDomain::Box) {
      apron_manager = new apron::box_manager;
    } else if(options.absint.domain == tapis::AbsIntDomain::Octagon) {
      apron_manager = new apron::oct_manager;
    } else if(options.absint.domain == tapis::AbsIntDomain::Polka) {
      apron_manager = new apron::polka_manager;
    } else {
      // TODO: THIS is unreachable
      return 10;
    }
    outputs.preanalysis_invariants = abstract_interpreter.analyze(*apron_manager);
    delete apron_manager;
  }

  //*- initialize the chosen engine and verify the program
  tapis::Engine *engine;
  if(options.engine == tapis::EngineKind::horn_ice_qdt) {
    engine = new tapis::HornICEQDT(module, clauses);
  } else if(options.engine == tapis::EngineKind::c_to_smtlib) {
    hcvc::ToSMTLIB tsmt2(clauses);
    tsmt2.transform();
    return 0;
  } else {
    // TODO: THIS is unreachable
    return 10;
  }
  engine->solve();
  delete engine;

  return 0;
}
