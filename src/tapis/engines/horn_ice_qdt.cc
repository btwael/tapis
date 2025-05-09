//
// Copyright (c) 2023 Wael-Amine Boutglay
//

#include "tapis/engines/horn_ice_qdt.hh"

#include "tapis/engines/options.hh"
#include "tapis/engines/hornice/hornice.hh"
#include "tapis/engines/hornice/qdt/learner.hh"
#include "tapis/engines/hornice/qdt/quantifier.hh"
#include "tapis/engines/hornice/qdt/general_qdt/classifier.hh"

namespace tapis {

  //*-- HornICEQDT
  HornICEQDT::HornICEQDT(hcvc::Module *module, hcvc::ClauseSet &clauses)
      : Engine(module, clauses) {}

  HornICEQDT::~HornICEQDT() = default;

  void HornICEQDT::solve() {
    std::set<const hcvc::Predicate *> predicates;
    auto cls = this->clauses().to_set();
    for(auto clause: cls) {
      for(const auto &app: clause->antecedent_preds()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(app);
        predicates.insert(casted->predicate());
      }
      if(clause->consequent()) {
        auto casted = std::dynamic_pointer_cast<hcvc::PredicateApplication>(*clause->consequent());
        predicates.insert(casted->predicate());
      }
    }
    HornICE::qdt::QuantifierManager quantifier_manager(get_options().ice.qdt.quantifier_numbers);
    quantifier_manager.set_context(this->module()->context());
    quantifier_manager.set_predicates(predicates);
    quantifier_manager.setup();

    HornICE::qdt::GeneralQDT::Classifier classifier(this->clauses(), predicates, quantifier_manager);

    auto learner = new HornICE::qdt::Learner(this->module(), this->clauses(), quantifier_manager, &classifier);
    HornICE::HornICE hice(this->module(), this->clauses(), learner);
    auto res = hice.verify();
    if(res == hcvc::VerifierResponse::SAFE) {
      std::cout << "SAFE\n";
    } else if(res == hcvc::VerifierResponse::UNSAFE) {
      std::cout << "UNSAFE\n";
    } else {
      std::cout << "UNKNOWN\n";
    }
  }

}
