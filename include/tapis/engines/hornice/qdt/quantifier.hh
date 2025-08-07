//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#pragma once

#include <set>
#include "hcvc/clause/predicate.hh"

namespace tapis::HornICE::qdt {

  //*-- QuantifierInfo
  class QuantifierInfo {
  public:
    const hcvc::Variable *quantifier;
    const hcvc::Variable *accessor;
    const hcvc::Predicate *predicate;
    const hcvc::Variable *array;
    const hcvc::Variable *size_variable;
  };

  //*-- QuantifierManager
  class QuantifierManager {
  public:
    QuantifierManager(unsigned long quantifier_per_array);

    ~QuantifierManager();

    //*- properties

    inline hcvc::Context &context() const {
      return *_context;
    }

    inline const std::vector<QuantifierInfo *> &quantifiers(const hcvc::Predicate *predicate) const {
      return _quantifiers.at(predicate);
    }

    inline const std::vector<QuantifierInfo *> &injected_accesses(const hcvc::Predicate *predicate) const {
      return _injected_access_variables.at(predicate);
    }

      inline const std::map<const hcvc::Variable *, std::vector<QuantifierInfo *>> &
  array_quantifiers(const hcvc::Predicate *predicate) const {
      // Use .at() to throw an exception if the predicate is not found, which is better than crashing.
      return _array_quantifiers.at(predicate);
  }

    //*- methods

    inline void set_context(hcvc::Context &context) {
      _context = &context;
    }

    void set_predicates(const std::set<const hcvc::Predicate *> &predicates);

    void setup();

    void increase(unsigned long N);

    /// Quantify the given formula for the predicate if quantifier are used.
    hcvc::Expr quantify(const hcvc::Predicate *predicate, hcvc::Expr body, bool only_substitute = false);

  private:
    unsigned long _quantifier_per_array;
    std::set<const hcvc::Predicate *> _predicates;
    std::map<const hcvc::Predicate *, std::vector<QuantifierInfo *>> _quantifiers; // WE can use this
    std::map<const hcvc::Predicate *, hcvc::Expr> _restrictions;
    std::map<const hcvc::Predicate *, std::vector<hcvc::Expr>> _quantifier_exprs;
    std::map<const hcvc::Predicate *, std::map<hcvc::Expr, hcvc::Expr>> _sub_maps;
    std::map<const hcvc::Predicate *, std::set<const hcvc::Variable *>> _quantifier_variables;
    std::map<const hcvc::Predicate *, std::set<const hcvc::Variable *>> _accessor_variables;
    std::map<const hcvc::Predicate *, std::map<const hcvc::Variable *, std::vector<QuantifierInfo *>>> _array_quantifiers; // 
    std::map<const hcvc::Predicate *, std::vector<QuantifierInfo *>> _injected_access_variables;

    unsigned long _qc = 0;

    hcvc::Context *_context;

    friend class DiagramManager;
  };

}
