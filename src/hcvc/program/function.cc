//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "hcvc/program/function.hh"

#include <utility>
#include "hcvc/module.hh"

namespace hcvc {

  //*-- Function
  Function::Function(std::string name, std::vector<Parameter *> parameters, const Type *return_type, Module *module)
      : _name(std::move(name)),
        _parameters(std::move(parameters)),
        _return_type(return_type),
        _return_variable(
            return_type->is_void() ? nullptr : Variable::create("!return", return_type, module->context(), true)),
        _module(module),
        _preconditionPredicate(FunctionPreconditionPredicate::create(this)),
        _summaryPredicate(FunctionSummaryPredicate::create(this)),
        _is_specified(false),
        _requirement(module->context().get_true()),
        _ensurement(module->context().get_true()) {
    // set the function for the parameters
    for(auto parameter: _parameters) {
      parameter->set_function(this);
    }
    // add the function to the module
    module->_functions[_name] = this;
  }

  Function::~Function() {
    // free the parameters
    for(auto parameter: _parameters) {
      delete parameter;
    }
  }

  Function *
  Function::create(std::string name, std::vector<Parameter *> parameters, const Type *returnType, Module *module) {
    return new Function(std::move(name), std::move(parameters), returnType, module);
  }
bool Function::has_predicate(const std::string &name) const {
    // Correctly access the map of predicates from the owning module
    return _module->_predicates.count(name) > 0;
}

}
