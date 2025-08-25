//
// Copyright (c) 2023 Wael-Amine Boutglay
//

#pragma once

#include <map>
#include <optional>
#include <set>
#include "hcvc/clause/clause.hh"
#include "hcvc/clause/predicate.hh"
#include "hcvc/clause/set.hh"
#include "tapis/engines/hornice/qdt/diagram.hh"
#include "tapis/engines/hornice/qdt/quantifier.hh"

namespace tapis::HornICE::qdt {

  //*-- Classifier
  class Classifier {
  public:
    Classifier(const hcvc::ClauseSet &clause_set, std::set<const hcvc::Predicate *> predicates,
               QuantifierManager &quantifier_manager, AggregationManager &aggregation_manager);

    virtual ~Classifier();

    //*- properties

    inline hcvc::ClauseSet clause_set() const {
      return _clause_set;
    }

    inline std::set<const hcvc::Predicate *> predicates() const {
      return _predicates;
    }

    inline QuantifierManager &quantifier_manager() const {
      return _quantifier_manager;
    }

    //*- methods

    virtual void resetup_attributes() = 0;

    virtual std::optional<std::unordered_map<const hcvc::Predicate *, hcvc::Expr>>
    classify(const DiagramPartialReachabilityGraph &diag_set) = 0;

  private:
    hcvc::ClauseSet _clause_set;
    std::set<const hcvc::Predicate *> _predicates;
    QuantifierManager &_quantifier_manager;
    AggregationManager& _aggregation_manager; 
  protected: 
    double _alpha;
    double _m_t = 0.0;
    double _v_t = 0.0;

  };

}
