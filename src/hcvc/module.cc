//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "hcvc/module.hh"

namespace hcvc {

  //*-- Module
  Module::Module(Context &context)
      : _context(context) {}

  Module::~Module() {
    // free declared functions
    for(const auto &[_, func]: _functions) {
      delete func;
    }
  }
// ... inside the hcvc namespace ...

Function* Module::get_function_owner(const Predicate* p) const {
    for (auto const& [name, func] : _functions) {
        if (func->has_predicate(p->name())) {
            return func;
        }
    }
    return nullptr;
}

Context& Module::context() {
  return _context;
}
}
