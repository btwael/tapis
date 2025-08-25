//
// Copyright (c) 2023 Wael-Amine Boutglay
//

#include "tapis/engines/horn_ice_qdt.hh"

#include "tapis/engines/options.hh"
#include "tapis/engines/hornice/hornice.hh"
#include "tapis/engines/hornice/qdt/learner.hh"
#include "tapis/engines/hornice/qdt/quantifier.hh"
#include "tapis/engines/hornice/qdt/aggregation.hh"
#include "tapis/engines/hornice/qdt/general_qdt/classifier.hh"
#include "tapis/engines/statistics.hh"
#include <memory>

namespace tapis {

  //*-- HornICEQDT
  HornICEQDT::HornICEQDT(hcvc::Module *module, hcvc::ClauseSet &clauses)
      : Engine(module, clauses) {}

  HornICEQDT::~HornICEQDT() = default;


void HornICEQDT::solve() {
    // Extract predicates from clauses
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

    // --- Start Manager Setup ---

    // 1. QuantifierManager on the stack
    HornICE::qdt::QuantifierManager quantifier_manager(get_options().ice.qdt.quantifier_numbers);
    quantifier_manager.set_context(this->module()->context());
    quantifier_manager.set_predicates(predicates);
    quantifier_manager.setup();

    // 2. AggregationManager on the stack
    HornICE::qdt::AggregationManager aggregation_manager(quantifier_manager);
    aggregation_manager.set_context(this->module()->context());
    aggregation_manager.set_predicates(predicates);
    aggregation_manager.setup();
    
    // 3. Classifier on the stack - now with AggregationManager
    HornICE::qdt::GeneralQDT::Classifier classifier(
        this->clauses(), 
        predicates, 
        quantifier_manager, 
        aggregation_manager
    );

    // 4. Learner on the heap, passed references to all managers
    auto learner = new HornICE::qdt::Learner(
        this->module(), 
        this->clauses(),
        &quantifier_manager,
        &aggregation_manager,
        &classifier
    );

    // --- End Manager Setup ---

    HornICE::HornICE hice(this->module(), this->clauses(), learner);
    auto res = hice.verify();


    std::cout << "------------------------\n";
    std::cout << "Verification finished in " << get_statistics().ice.iterations << " iterations.\n";

    if (res == hcvc::VerifierResponse::SAFE) {
        std::cout << "SAFE\n";
    } else if (res == hcvc::VerifierResponse::UNSAFE) {
        std::cout << "UNSAFE\n";
    } else {
        std::cout << "UNKNOWN\n";
    }

    delete learner;
}
}
