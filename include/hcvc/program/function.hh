//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#pragma once

#include <string>
#include <vector>
#include "hcvc/module.hh"
#include "hcvc/clause/predicate.hh"
#include "hcvc/program/type.hh"
#include "hcvc/program/variable.hh"

namespace hcvc {

  class Module;

  class Parameter;

  class FunctionPreconditionPredicate;

  class FunctionSummaryPredicate;

  //*-- Function
  /**
   * A function in the program in the target language, for which we may need to synthesize a precondition and summary,
   * and also invariants for the loops in its body.
   */
  class Function {
    Function(std::string name, std::vector<Parameter *> parameters, const Type *return_sort, Module *module);

  public:
    /**
     * Destructor of `Function`.
     *
     * Notice: - it frees the function's parameters.
     */
    ~Function();

    //*- properties

    /// Get the module in which this function is declared.
    inline Module *module() const {
      return _module;
    }

    /// Get the name of the function.
    inline const std::string &name() const {
      return _name;
    }

    /// Get the parameters of the function.
    inline const std::vector<Parameter *> &parameters() const {
      return _parameters;
    }

    /// Get the precondition's predicate of the function
    inline FunctionPreconditionPredicate *precondition_pred() const {
      return _preconditionPredicate;
    }

    /// Get the summary's predicate of the function
    inline FunctionSummaryPredicate *summary_pred() const {
      return _summaryPredicate;
    }

    /// Get the return type of the function.
    inline const Type *return_type() const {
      return _return_type;
    }

    /// Get the return variable of the function.
    inline Variable *return_variable() const {
      return _return_variable;
    }

    /// Get whether the function is specified
    inline bool is_specified() const {
      return _is_specified;
    }

    inline hcvc::Expr get_ensurement() {
      return _ensurement;
    }

    inline hcvc::Expr get_requirement() {
      return _requirement;
    }

    //*- methods

    inline void add_requirement(hcvc::Expr f) {
      _is_specified = true;
      _requirement = _requirement && f;
    }

    inline void add_ensurement(hcvc::Expr f) {
      _is_specified = true;
      _ensurement = _ensurement && f;
    }

    //*- statics

    /// Create a function of given name with given parameters and return types in the given module.
    static Function *
    create(std::string name, std::vector<Parameter *> parameters, const Type *returnType, Module *module);

    bool has_predicate(const std::string& name) const;
      Variable* find_local_variable(const std::string& name) const;

  private:
    std::string _name;
    std::vector<Parameter *> _parameters;
    const Type *_return_type;
    Variable *_return_variable;
    Module *_module;

    FunctionPreconditionPredicate *_preconditionPredicate;
    FunctionSummaryPredicate *_summaryPredicate;

    bool _is_specified;
    hcvc::Expr _requirement;
    hcvc::Expr _ensurement;
  };

}
