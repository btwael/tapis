//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#pragma once

#include <map>
#include <string>
#include "hcvc/context.hh"
#include "hcvc/clause/hypergraph.hh"
#include "hcvc/program/function.hh"

namespace hcvc {

  class Function;

  //*-- Module
  class Module {
  public:
    Module(Context &context);

    /**
     * Notice: - it frees all the declared functions.
     */
    ~Module();

    //*- properties

    /// Get the HCVC context.
    inline Context &context() const {
      return _context;
    }

    /// Get the clauses' hypergraph.
    HyperGraph &hypergraph() {
      return _hypergraph;
    }

    //*- methods

    /// Get the function with given name if it exists
    inline Function *get_function(const std::string &name) const {
      if(_functions.count(name) > 0) {
        return _functions.at(name);
      }
      return nullptr;
    }

    /// Get the predicate with given name if it exists
    inline const Predicate *get_predicate(const std::string &name) const {
      if(_predicates.count(name) > 0) {
        return _predicates.at(name);
      }
      return nullptr;
    }

      Function* get_function_owner(const Predicate* p) const;
      Context& context(); // Add a getter for the context

  private:
    Context &_context;
    std::map<std::string, Function *> _functions;
    std::map<std::string, Predicate *> _predicates;
    HyperGraph _hypergraph;

    //*- friends

    friend class Function;

    friend class InvariantPredicate;

    friend class FunctionPreconditionPredicate;

    friend class FunctionSummaryPredicate;
  };

}
