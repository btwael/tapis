//
// Copyright (c) 2023 Wael-Amine Boutglay
//

#include <cstdlib>
#include <iostream>
#include <string>
#include "sexpresso.hpp"
#include "hcvc/logic/term.hh"
#include "hcvc/program/function.hh"

namespace hcvc::fe::c {

  class Scope;

  bool is_number(const std::string &s) {
    std::string::const_iterator it = s.begin();
    while(it != s.end() && std::isdigit(*it)) ++it;
    return !s.empty() && it == s.end();
  }

  hcvc::Parameter *find_parameter(const std::string & name, std::vector<hcvc::Parameter *> parameters) {
    for(auto parameter: parameters) {
      if(parameter->name() == name) {
        return parameter;
      }
    }
    return nullptr;
  }

  class SpecParser {
  public:
    SpecParser(const std::string &str, Scope *scope, hcvc::Context &context)
        : _scope(scope),
          _tree(sexpresso::parse(str)),
          _context(context) {}

    hcvc::Expr parse() {
      std::map<std::string, hcvc::Expr> scope;
      return parse(_tree, scope);
    }

    hcvc::Expr parse(sexpresso::Sexp node, std::map<std::string, hcvc::Expr> &scope) {
      switch(node.kind) {
        case sexpresso::SexpValueKind::SEXP:
          if(node.value.sexp.size() == 1) {
            return parse(node.value.sexp[0], scope);
          } else {
            assert(!node.value.sexp[0].isSexp());
            auto op = node.value.sexp[0].value.str;
            /*if(op == "[].size") {
              auto var_name = node.value.sexp[1].value.str;
              auto parameter = find_parameter(var_name, _function->parameters());
              return hcvc::VariableConstant::create(parameter->size_variable(), 0, _context);
            } else*/
            if(op == "forall") {
              std::vector<hcvc::Expr> qvars;
              assert(node.value.sexp[1].isSexp());
              auto new_scope = scope;
              for(unsigned int i = 0, lengthi = node.value.sexp[1].value.sexp.size(); i < lengthi; i++) {
                assert(node.value.sexp[1].value.sexp[i].isSexp());
                assert(node.value.sexp[1].value.sexp[i].value.sexp[0].isString());
                assert(node.value.sexp[1].value.sexp[i].value.sexp[1].isString());
                auto qvar_name = node.value.sexp[1].value.sexp[i].value.sexp[0].value.str;
                auto qvar_type = node.value.sexp[1].value.sexp[i].value.sexp[1].value.str;
                const hcvc::Type *type;
                if(qvar_type == "Int") {
                  type = _context.type_manager().int_type();
                }
                auto cnst = hcvc::Constant::create(qvar_name, type, _context);
                new_scope.emplace(qvar_name, cnst);
                qvars.push_back(cnst);
              }
              return hcvc::QuantifiedFormula::create(hcvc::Quantifier::ForAll, qvars, parse(node.value.sexp[2], new_scope), _context);
            } else if(op == "exists") {
              std::vector<hcvc::Expr> qvars;
              assert(node.value.sexp[1].isSexp());
              auto new_scope = scope;
              for(unsigned int i = 0, lengthi = node.value.sexp[1].value.sexp.size(); i < lengthi; i++) {
                assert(node.value.sexp[1].value.sexp[i].isSexp());
                assert(node.value.sexp[1].value.sexp[i].value.sexp[0].isString());
                assert(node.value.sexp[1].value.sexp[i].value.sexp[1].isString());
                auto qvar_name = node.value.sexp[1].value.sexp[i].value.sexp[0].value.str;
                auto qvar_type = node.value.sexp[1].value.sexp[i].value.sexp[1].value.str;
                const hcvc::Type *type;
                if(qvar_type == "Int") {
                  type = _context.type_manager().int_type();
                }
                auto cnst = hcvc::Constant::create(qvar_name, type, _context);
                new_scope.emplace(qvar_name, cnst);
                qvars.push_back(cnst);
              }
              return hcvc::QuantifiedFormula::create(hcvc::Quantifier::Exists, qvars, parse(node.value.sexp[2], new_scope), _context);
            } else {
              std::vector<hcvc::Expr> args;
              for(unsigned long i = 1, lengthi = node.value.sexp.size(); i < lengthi; i++) {
                args.push_back(parse(node.value.sexp[i], scope));
              }
              return _context.apply(op, args);
            }
          }
          break;
        case sexpresso::SexpValueKind::STRING:
          auto value = node.value.str;
          if(value == "true") {
            return _context.get_true();
          } else if(value == "false") {
            return _context.get_false();
          } else if(is_number(value)) {
            return hcvc::IntegerLiteral::get(value, _context.type_manager().int_type(), _context);
          } else {
            if(scope.count(value) > 0) {
              return scope.at(value);
            }
            auto variable = _scope->get_variable_by_name(value);
            if(variable != nullptr) {
              return _scope->get(variable);
            }
            std::cerr << "Error: Unknown identifier '" << value << "' in specification string." << std::endl;
            exit(1);
          }
      }
      return _context.get_false();
    }

  private:
    Scope *_scope;
    sexpresso::Sexp _tree;
    hcvc::Context &_context;
  };

}
