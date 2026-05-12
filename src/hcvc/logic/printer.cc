//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include "hcvc/logic/printer.hh"

#include "hcvc/clause/clause.hh"
#include "hcvc/clause/predicate.hh"

namespace hcvc {

  // Printer
  Printer::Printer() = default;

  std::string Printer::to_string(const Expr &expr) {
    expr->accept(*this);
    return result();
  }

  void Printer::visit(std::shared_ptr<OperatorApplication> term) {
    auto res = "(" + term->operat0r()->name();
    if(term->operat0r()->name() == "[]") {
      if(term->arguments().size() == 2) {
        res = "(select";
      } else {
        res = "(store";
      }
    }
    for(const auto &arg: term->arguments()) {
      if(arg != nullptr) {
        arg->accept(*this);
        res += " " + result();
      } else {
        res += " <null>";
      }
    }
    return _return(res + ")");
  }

  inline bool _is_special(char c) {
    return c == '_' || c == '+' || c == '-' || c == '*' || c == '&' || c == '|' || c == '!' || c == '~' || c == '<' ||
           c == '>' || c == '=' || c == '/' || c == '?' || c == '.' || c == '$' || c == '^';
  }

  bool _is_simple_symbol(const std::string &symbol) {
    return std::all_of(symbol.begin(), symbol.end(), [](char c) {
      return ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || _is_special(c);
    });
  }

  void Printer::visit(std::shared_ptr<Constant> term) {
    if(_is_simple_symbol(term->name())) {
      return _return(term->name());
    } else {
      return _return("|" + term->name() + "|");
    }
  }

  void Printer::visit(std::shared_ptr<BooleanLiteral> term) {
    if(term->value()) {
      return _return("true");
    }
    return _return("false");
  }

  void Printer::visit(std::shared_ptr<IntegerLiteral> term) {
    long long val = std::stoll(term->value());
    if(val < 0) {
      return _return("(- " + std::to_string(-val) + ")");
    }
    return _return(term->value());
  }

  void Printer::visit(std::shared_ptr<ArrayLiteral> term) {
    std::string res = "[";
    for(unsigned long i = 0, size = term->values().size(); i < size; i++) {
      term->values()[i]->accept(*this);
      res += result();
      if(i != size - 1) {
        res += ",";
      }
    }
    res += "]";
    return _return(res);
  }

  void Printer::visit(std::shared_ptr<QuantifiedFormula> term) {
    std::string res = "(";
    if(term->quantifier_kind() == Quantifier::ForAll) {
      res += "forall ";
    } else if(term->quantifier_kind() == Quantifier::Exists) {
      res += "exists ";
    }
    res += "(";
    for(const auto &var: term->quantifiers()) {
      auto v = std::dynamic_pointer_cast<Constant>(var);
      res += "(" + v->name() + " ";
      if(v->type()->is_int()) {
        res += "Int";
      } else if(v->type()->is_array()) {
        res += "(Array Int Int)";
      } else {
        res += "Bool";
      }
      res += ")";
    }
    res += ")";
    term->formula()->accept(*this);
    res += " " + result();
    return _return(res + ")");
  }

  void Printer::visit(std::shared_ptr<PredicateApplication> term) {
    auto res = "(" + term->predicate()->name();
    for(const auto &arg: term->arguments()) {
      if(arg != nullptr) {
        arg->accept(*this);
        res += " " + result();
      } else {
        res += " <null>";
      }
    }
    return _return(res + ")");
  }

}
