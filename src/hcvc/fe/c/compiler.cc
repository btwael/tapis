//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#include <utility>

#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CallGraph.h"
#include "clang/Tooling/Tooling.h"
#include "hcvc/module.hh"
#include "hcvc/clause/clause.hh"
#include "hcvc/logic/term.hh"
#include "tapis/engines/options.hh"

namespace hcvc::fe::c {
  //*-- Scope
  class Scope {
  public:
    explicit Scope(hcvc::Context &context)
        : _context(context) {}

    //*- methods

    void put(hcvc::Variable *variable) {
      _variables.push_back(variable);
      _v[variable] = hcvc::VariableConstant::create(variable, 0, _context);
    }

    void set(hcvc::Variable *variable, hcvc::Expr expr) {
      _v[variable] = std::move(expr);
    }

    hcvc::Expr get(hcvc::Variable *variable) {
      return _v[variable];
    }

    void reset() {
      for(auto variable: _variables) {
        _v[variable] = hcvc::VariableConstant::create(variable, 0, _context);
      }
    }

    hcvc::Variable *get_variable_by_name(const std::string &name) {
      for(auto var: _variables) {
        if(var->name() == name) {
          return var;
        }
      }
      return nullptr;
    }

    const std::vector<hcvc::Variable *> &get_variables() const {
      return _variables;
    }

    bool is_initialized(hcvc::Variable *variable) {
      return _init_values.count(variable) > 0;
    }

    void put_initialization(hcvc::Variable *variable, hcvc::Expr value) {
      _init_values[variable] = value;
    }

    hcvc::Expr get_initialization(hcvc::Variable *variable) {
      return _init_values[variable];
    }

  private:
    hcvc::Context &_context;
    std::vector<hcvc::Variable *> _variables;
    std::unordered_map<hcvc::Variable *, hcvc::Expr> _v;
    std::unordered_map<hcvc::Variable *, hcvc::Expr> _init_values;
  };
}

#include "spec_parser.cc"

namespace hcvc::fe::c {

  static unsigned long _ret_counter = 0;
  static unsigned long _loop_counter = 0;
  static unsigned long _ifpost_counter = 0;

  const hcvc::Type *compile_type(clang::QualType clang_type, hcvc::Context &context) {
    if(clang_type->isPointerType()) {
      return context.type_manager().get_array_type(compile_type(clang_type->getPointeeType(), context));
    } else if(clang_type->isBooleanType() || (clang_type->isTypedefNameType() && clang_type.getAsString() == "bool")) {
      return context.type_manager().bool_type();
    } else if(clang_type->isIntegerType()) {
      if(clang_type->isSignedIntegerType()) {
        return context.type_manager().int_type();
      } else {
        return context.type_manager().uint_type();
      }
    } else if(clang_type->isVoidType()) {
      return context.type_manager().void_type();
    }
    return context.type_manager().int_type();
  }

  class State {
  public:
    State(hcvc::Module &module, hcvc::Context &context)
        : _context(context), _scope(context), _module(module) {
    }

    Scope &scope() {
      return _scope;
    }

    void assume(const hcvc::Expr &term) {
      _phi.push_back(term);
    }

    void assume(hcvc::Predicate *predicate) {
      std::vector<hcvc::Expr> arguments;
      arguments.reserve(predicate->parameters().size());
      for(auto variable: predicate->parameters()) {
        arguments.push_back(this->scope().get(variable));
      }
      _pred_apps.emplace_back(std::make_shared<hcvc::PredicateApplication>(predicate, arguments, _context));
    }

    void assume(hcvc::Predicate *predicate, const std::vector<hcvc::Expr> &arguments) {
      _pred_apps.emplace_back(std::make_shared<hcvc::PredicateApplication>(predicate, arguments, _context));
    }

    void then(hcvc::Predicate *predicate) {
      std::vector<hcvc::Expr> arguments;
      arguments.reserve(predicate->parameters().size());
      for(auto variable: predicate->parameters()) {
        arguments.push_back(this->scope().get(variable));
      }
      auto consequent = std::make_shared<hcvc::PredicateApplication>(predicate, arguments, _context);
      auto clause = new hcvc::Clause(_pred_apps, {_phi}, std::make_optional(consequent), _context);
      _module.hypergraph().add(clause);
    }

    void then(hcvc::Predicate *predicate, const std::vector<hcvc::Expr> &arguments) {
      auto consequent = std::make_shared<hcvc::PredicateApplication>(predicate, arguments, _context);
      auto clause = new hcvc::Clause(_pred_apps, {_phi}, std::make_optional(consequent), _context);
      _module.hypergraph().add(clause);
    }

    void assure(const hcvc::Expr &expr, hcvc::Weakness weakness) {
      std::vector<hcvc::Expr> phi = _phi;
      phi.push_back(!expr);
      auto clause = new hcvc::Clause(_pred_apps, phi, std::nullopt, _context);
      _module.hypergraph().add(clause, weakness);
    }

    void reset() {
      this->scope().reset();
      _phi.clear();
      _pred_apps.clear();
    }

    bool compile(clang::Stmt *stmt, hcvc::Function *function) {
      if(stmt == nullptr) {
        return false;
      }
      if(stmt->getStmtClass() == clang::Stmt::BreakStmtClass) {
        return compile((clang::BreakStmt *) stmt, function);
      } else if(stmt->getStmtClass() == clang::Stmt::CompoundStmtClass) {
        return compile((clang::CompoundStmt *) stmt, function);
      } else if(stmt->getStmtClass() == clang::Stmt::DeclStmtClass) {
        return compile((clang::DeclStmt *) stmt, function);
      } else if(stmt->getStmtClass() == clang::Stmt::ForStmtClass) {
        return compile((clang::ForStmt *) stmt, function);
      } else if(stmt->getStmtClass() == clang::Stmt::IfStmtClass) {
        return compile((clang::IfStmt *) stmt, function);
      } else if(stmt->getStmtClass() == clang::Stmt::ReturnStmtClass) {
        return compile((clang::ReturnStmt *) stmt, function);
      } else if(stmt->getStmtClass() == clang::Stmt::WhileStmtClass) {
        return compile((clang::WhileStmt *) stmt, function);
      } else { // expression statement
        // TODO: this else may take other stuff other than Expression Statement; add other cases
        auto expr = clang::dyn_cast<clang::Expr>(stmt);
        if(expr == nullptr) {
          stmt->dump();
          std::cout << "IMPL-MISSING in Stmt compiler: Unhandled statement type." << std::endl;
          exit(10);
        }
        compile(expr, function);
        return false;
      }
    }

    bool compile(clang::BreakStmt *stmt, hcvc::Function *function) {
      this->then(_loop_invariant_stack.top());
      this->assume(_context.get_false());
      return false;
    }

    bool compile(clang::CompoundStmt *stmt, hcvc::Function *function) {
      for(clang::Stmt *statement: stmt->body()) {
        compile(statement, function);
        if(statement->getStmtClass() == clang::Stmt::ReturnStmtClass) {
          return true;
        }
      }
      return false;
    }

    bool compile(clang::DeclStmt *stmt, hcvc::Function *function) {
      for(auto decl: stmt->decls()) {
        auto var_decl = dynamic_cast<clang::VarDecl *>(decl);
        if(var_decl->getType()->isArrayType()) {
          auto var_type = var_decl->getType()->getAsArrayTypeUnsafe();
          auto array_sort = _context.type_manager().get_array_type(compile_type(var_type->getElementType(), _context));
          auto variable = hcvc::Variable::create(var_decl->getNameAsString(), array_sort, _context);
          hcvc::Expr size;
          if(auto vla_type = clang::dyn_cast<clang::VariableArrayType>(var_type)) {
            size = compile(vla_type->getSizeExpr(), function);
          } else if(auto constant_array_type = clang::dyn_cast<clang::ConstantArrayType>(var_type)) {
            auto size_str = llvm::toString(constant_array_type->getSize(), 10, true);
            size = hcvc::IntegerLiteral::get(size_str, _context.type_manager().int_type(), _context);
          } else {
            var_type->dump();
            std::cout << "IMPL-MISSING in DeclStmt compiler: Unhandled array type." << std::endl;
            exit(10);
          }
          bool is_size_set = false;
          if(size->kind() == hcvc::TermKind::Constant) {
            auto cnst = std::dynamic_pointer_cast<hcvc::Constant>(size);
            if(cnst->is_variable_constant()) {
              is_size_set = true;
              variable->carry_size_variable(
                  (hcvc::Variable *) std::dynamic_pointer_cast<hcvc::VariableConstant>(cnst)->variable());
            }
          }
          if(!is_size_set) {
            variable->carry_size_variable();
          }
          this->scope().put(variable);
          if(!is_size_set) {
            this->scope().put(variable->size_variable());
            this->assume(this->scope().get(variable->size_variable()) == size);
          }
          // TODO: initialized arrays
        } else {
          auto variable = hcvc::Variable::create(var_decl->getNameAsString(),
                                                 compile_type(var_decl->getType(), _context), _context);
          this->scope().put(variable);
          if(var_decl->hasInit()) {
            auto init = compile(var_decl->getInit(), function);
            this->assume(this->scope().get(variable) == init);
            if(!this->scope().is_initialized(variable)) {
              this->scope().put_initialization(variable, init);
            }
            // announce that assigned variable is a data variable, if it's assigned with a data element
            if(init->kind() == hcvc::TermKind::OpApp &&
               std::dynamic_pointer_cast<hcvc::OperatorApplication>(init)->operat0r()->name() == "[]") {
              variable->set_is_data();
            }
          }
        }
      }
      return false;
    }

    enum class QuantifiableForType {
      Assert,
      Assume
    };

    std::pair<bool, std::optional<QuantifiableForType>> _is_quantifiable_for(clang::Stmt *body) {
      if(body->getStmtClass() == clang::Stmt::CallExprClass) {
        auto func_name = ((clang::CallExpr *) body)->getDirectCallee()->getNameAsString();
        return std::make_pair(func_name == "assert" || func_name == "assume",
                              std::make_optional(
                                  func_name == "assert" ? QuantifiableForType::Assert : QuantifiableForType::Assume));
      } else if(body->getStmtClass() == clang::Stmt::CompoundStmtClass) {
        auto comp_stmt = (clang::CompoundStmt *) body;
        auto res = _is_quantifiable_for(*comp_stmt->body_begin());
        return std::make_pair(comp_stmt->size() == 1 && res.first, res.second);
      } else if(body->getStmtClass() == clang::Stmt::ForStmtClass) {
        return _is_quantifiable_for(((clang::ForStmt *) body)->getBody());
      }
      return std::make_pair(false, std::nullopt);
    }

    std::vector<std::pair<std::string, hcvc::Expr>> _get_for_init_vars(clang::Stmt *stmt, State *state) {
      std::vector<std::pair<std::string, hcvc::Expr>> res;
      if(stmt->getStmtClass() == clang::Stmt::DeclStmtClass) {
        auto decl_stmt = (clang::DeclStmt *) stmt;
        for(auto decl: decl_stmt->decls()) {
          auto var_decl = dynamic_cast<clang::VarDecl *>(decl);
          if(var_decl->isUsed()) {
            if(var_decl->hasInit()) {
              res.emplace_back(var_decl->getNameAsString(), state->compile(var_decl->getInit()));
            } else {
              res.emplace_back(var_decl->getNameAsString(),
                               hcvc::IntegerLiteral::get("0", compile_type(var_decl->getType(), _context), _context));
            }
          }
        }
      }
      return res;
    }

    std::pair<std::vector<hcvc::Expr>, hcvc::Expr> _compile_quantifiable_for(clang::Stmt *body, State *state) {
      if(body->getStmtClass() == clang::Stmt::CallExprClass) { // this is an assert
        auto call_expr = (clang::CallExpr *) body;
        return std::make_pair(std::vector<hcvc::Expr>(), state->compile(call_expr->getArg(0)));
      } else if(body->getStmtClass() == clang::Stmt::CompoundStmtClass) {
        auto comp_stmt = (clang::CompoundStmt *) body;
        return _compile_quantifiable_for(*comp_stmt->body_begin(), state);
      } else if(body->getStmtClass() == clang::Stmt::ForStmtClass) {
        auto for_stmt = (clang::ForStmt *) body;
        auto guard = _context.get_true();
        auto clone = new State(*state);
        clone->compile(for_stmt->getInit(), nullptr);
        std::vector<hcvc::Expr> quantified;
        auto variables = _get_for_init_vars(for_stmt->getInit(), clone);
        for(const auto &pair: variables) {
          auto variable = clone->scope().get(clone->scope().get_variable_by_name(pair.first));
          quantified.push_back(variable);
          guard = guard && _context.apply("<=", {pair.second, variable});
        }
        guard = guard && clone->compile(for_stmt->getCond());
        auto res = _compile_quantifiable_for(for_stmt->getBody(), clone);
        for(const auto &el: res.first) {
          quantified.push_back(el);
        }
        delete clone;
        return std::make_pair(quantified, _context.apply("=>", {guard, res.second}));
      }
      return std::make_pair(std::vector<hcvc::Expr>(), _context.get_false());
    }

    bool compile(clang::ForStmt *stmt, hcvc::Function *function) {
      if(tapis::get_options().chc_quantify_for_assert) {
        auto quantification = _is_quantifiable_for(stmt);
        if(quantification.first) {
          // TODO: fix index our of bound generated with this
          auto res = _compile_quantifiable_for(stmt, this);
          auto quantified = hcvc::QuantifiedFormula::create(hcvc::Quantifier::ForAll, res.first, res.second, _context);
          if(*(quantification.second) == QuantifiableForType::Assert) {
            this->assure(quantified, hcvc::Weakness::assertion_violation);
          }
          this->assume(quantified);
          return false;
        }
      }
      compile(stmt->getInit(), function);
      auto inv_pred = hcvc::InvariantPredicate::create(function, "!inv" + std::to_string(_loop_counter++),
                                                       scope().get_variables());
      // emit clauses (precondition => inv)
      this->then(inv_pred);

      this->reset();
      this->assume(inv_pred);
      auto cond_s = compile(stmt->getCond(), function);
      this->assume(cond_s);
      _loop_invariant_stack.push(inv_pred);
      compile(stmt->getBody(), function);
      compile(stmt->getInc(), function);
      _loop_invariant_stack.pop();
      this->then(inv_pred);
      for(auto v: get_potential_segment_variable(stmt->getInc())) {
        inv_pred->add_segment_variable(v);
        if(this->scope().is_initialized(v)) {
          auto vars = get_variables(this->scope().get_initialization(v));
          for(auto va: vars) {
            inv_pred->add_segment_variable(va);
          }
        }
      }
      for(auto v: get_potential_segment_variable(stmt->getBody())) {
        inv_pred->add_segment_variable(v);
      }

      this->reset();
      this->assume(inv_pred);
      auto cond_n = compile(stmt->getCond(), function);
      this->assume(!cond_n);
      return false;
    }

    std::vector<hcvc::Variable *> get_potential_segment_variable(clang::Stmt *body) {
      std::vector<hcvc::Variable *> res;
      std::stack<clang::Stmt *> stack;
      stack.push(body);
      while(!stack.empty()) {
        // pop
        auto elem = stack.top();
        stack.pop();
        // process
        if(elem == nullptr) continue;
        // check if it's an assignment
        if(elem->getStmtClass() == clang::Stmt::UnaryOperatorClass) {
          auto casted = (clang::UnaryOperator *) elem;
          if(casted->getOpcode() == clang::UnaryOperatorKind::UO_PostInc ||
             casted->getOpcode() == clang::UnaryOperatorKind::UO_PostDec) { // TODO: other operator v = v + 1...
            auto var_name = ((clang::DeclRefExpr *) casted->getSubExpr())->getDecl()->getNameAsString();
            // get variable in the scope with that name
            auto variable = this->scope().get_variable_by_name(var_name);
            res.push_back(variable);
          }
        }
        // push children to the stack
        for(auto subelem: elem->children()) {
          if(subelem->getStmtClass() != clang::Stmt::ForStmtClass &&
             subelem->getStmtClass() != clang::Stmt::WhileStmtClass) {
            stack.push(subelem);
          }
        }
      }
      return res;
    }

    bool compile(clang::IfStmt *stmt, hcvc::Function *function) {
      auto ifpost_pred = hcvc::InvariantPredicate::create(function, "!ifpost" + std::to_string(_ifpost_counter++),
                                                          scope().get_variables());
      _module.hypergraph().add_to_be_simplified(ifpost_pred);
      auto cond_s = compile(stmt->getCond(), function);
      State *state_c = new State(*this);
      state_c->assume(cond_s);
      if(!state_c->compile(stmt->getThen(), function)) {
        state_c->then(ifpost_pred);
      }
      delete state_c;
      if(stmt->hasElseStorage()) {
        State *state_nc = new State(*this);
        state_nc->assume(!cond_s);
        if(!state_nc->compile(stmt->getElse(), function)) {
          state_nc->then(ifpost_pred);
        }
        delete state_nc;
      } else {
        this->assume(!cond_s);
        this->then(ifpost_pred);
      }

      this->reset();
      this->assume(ifpost_pred);
      return false;
    }

    bool compile(clang::ReturnStmt *stmt, hcvc::Function *function) {
      if(function->return_variable() != nullptr) {
        this->scope().put(function->return_variable());
        auto compiled = compile(stmt->getRetValue(), function);
        if(compiled->kind() == TermKind::Constant) {
          auto casted = std::dynamic_pointer_cast<hcvc::Constant>(compiled);
          if(casted->is_variable_constant()) {
            auto casted2 = std::dynamic_pointer_cast<hcvc::VariableConstant>(compiled);
            if(casted2->variable()->is_data()) {
              function->return_variable()->set_is_data();
            }
          }
        }
        this->assume(this->scope().get(function->return_variable()) == compiled);
      }
      // emit clauses
      this->then(function->summary_pred());
      return true;
    }

    bool compile(clang::WhileStmt *stmt, hcvc::Function *function) {
      auto inv_pred = hcvc::InvariantPredicate::create(function, "!inv" + std::to_string(_loop_counter++),
                                                       scope().get_variables());
      // emit clauses (precondition => inv)
      this->then(inv_pred);

      this->reset();
      this->assume(inv_pred);
      auto cond_s = compile(stmt->getCond(), function);
      this->assume(cond_s);
      _loop_invariant_stack.push(inv_pred);
      compile(stmt->getBody(), function);
      _loop_invariant_stack.pop();
      this->then(inv_pred);
      for(auto v: get_potential_segment_variable(stmt->getBody())) {
        inv_pred->add_segment_variable(v);
      }

      this->reset();
      this->assume(inv_pred);
      auto cond_n = compile(stmt->getCond(), function);
      this->assume(!cond_n);
      return false;
    }

    hcvc::Expr compile(clang::Expr *expr, hcvc::Function *function = nullptr) {
      //std::cout << expr->getStmtClassName() << "\n";
      if(expr->getStmtClass() == clang::Stmt::ArraySubscriptExprClass) {
        return compile((clang::ArraySubscriptExpr *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::BinaryOperatorClass) {
        return compile((clang::BinaryOperator *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::CallExprClass) {
        return compile((clang::CallExpr *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::DeclRefExprClass) {
        return compile((clang::DeclRefExpr *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::ImplicitCastExprClass) {
        return compile((clang::ImplicitCastExpr *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::IntegerLiteralClass) {
        return compile((clang::IntegerLiteral *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::ParenExprClass) {
        return compile((clang::ParenExpr *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::UnaryOperatorClass) {
        return compile((clang::UnaryOperator *) expr, function);
      } else if(expr->getStmtClass() == clang::Stmt::NullStmtClass) {
        return _context.get_true();
      } else {
        expr->dump();
        std::cout << "IMPL-MISSING" << "\n";
        exit(10);
      }
      return _context.get_false();
    }

    hcvc::Expr compile(clang::ArraySubscriptExpr *expr, hcvc::Function *function = nullptr) {
      // get array variable name
      auto var_name = ((clang::DeclRefExpr *) ((clang::ImplicitCastExpr *) expr->getBase())->getSubExpr())->getDecl()->getNameAsString();
      // get variable from the scope with that name
      auto variable = this->scope().get_variable_by_name(var_name);
      auto size_variable_cnst = this->scope().get(variable->size_variable());
      auto array = compile(expr->getBase(), function);
      auto index = compile(expr->getIdx(), function);
      // emit clauses (index < 0)
      this->assure(_context.apply(">=", {index, hcvc::IntegerLiteral::get("0", size_variable_cnst->type(), _context)}),
                   hcvc::Weakness::buffer_under_read);
      // emit clauses (index >= array.size)
      this->assure(_context.apply("<", {index, size_variable_cnst}), hcvc::Weakness::buffer_over_read);
      return _context.apply("[]", {array, index});
    }

    hcvc::Expr compile(clang::BinaryOperator *expr, hcvc::Function *function = nullptr) {
      if(expr->getOpcode() == clang::BinaryOperatorKind::BO_Assign) {
        auto lhs = expr->getLHS();
        auto compiled_lhs = _context.get_true();
        auto compiled_rhs = compile(expr->getRHS(), function);
        if(lhs->getStmtClass() == clang::Stmt::DeclRefExprClass) { // a variable is assigned
          // get assigned variable name
          auto var_name = ((clang::DeclRefExpr *) lhs)->getDecl()->getNameAsString();
          // get variable in the scope with that name
          auto variable = this->scope().get_variable_by_name(var_name);
          if(!this->scope().is_initialized(variable)) {
            this->scope().put_initialization(variable, compiled_rhs);
          }
          // compute the next constant for that variable
          compiled_lhs = std::dynamic_pointer_cast<hcvc::VariableConstant>(
              this->scope().get(variable))->next();
          // assign new_const to that variable
          this->scope().set(variable, compiled_lhs);
          // announce that assigned variable is a data variable, if it's assigned with a data element
          if(compiled_rhs->kind() == hcvc::TermKind::OpApp &&
             std::dynamic_pointer_cast<hcvc::OperatorApplication>(compiled_rhs)->operat0r()->name() == "[]") {
            variable->set_is_data();
          }
        } else if(lhs->getStmtClass() == clang::Stmt::ArraySubscriptExprClass) { // an array element is assigned
          // get assigned variable name
          auto subscript = (clang::ArraySubscriptExpr *) lhs;
          auto var_name = ((clang::DeclRefExpr *) ((clang::ImplicitCastExpr *) subscript->getBase())->getSubExpr())->getDecl()->getNameAsString();
          // get variable in the scope with that name
          auto variable = this->scope().get_variable_by_name(var_name);
          // get the old constant of the variable
          auto old_cnst = this->scope().get(variable);
          // compute the next constant for that variable
          compiled_lhs = std::dynamic_pointer_cast<hcvc::VariableConstant>(this->scope().get(variable))->next();
          // compile index
          auto index = compile(subscript->getIdx(), function);
          // compile the assignment
          compiled_rhs = _context.apply("[]", {old_cnst, index, compiled_rhs});
          // assign new_const to that variable
          this->scope().set(variable, compiled_lhs);
          // Detect buffer (over- and under-)write
          auto size_variable_cnst = this->scope().get(variable->size_variable());
          // emit clauses (index < 0)
          this->assure(
              _context.apply(">=", {index, hcvc::IntegerLiteral::get("0", size_variable_cnst->type(), _context)}),
              hcvc::Weakness::buffer_under_write);
          // emit clauses (index >= array.size)
          this->assure(_context.apply("<", {index, size_variable_cnst}), hcvc::Weakness::buffer_over_write);
        } else {
          std::cout << "IMPL-MISSING" << "\n";
          exit(10);
        }
        this->assume(compiled_lhs == compiled_rhs);
        return compiled_lhs;
      } else {
        // compile the arguments
        std::vector<hcvc::Expr> arguments = {
            compile(expr->getLHS(), function),
            compile(expr->getRHS(), function)
        };
        std::string op_name;
        if(arguments[0]->kind() == hcvc::TermKind::Constant &&
           std::dynamic_pointer_cast<hcvc::Constant>(arguments[0])->is_variable_constant() &&
           arguments[1]->kind() == hcvc::TermKind::OpApp &&
           std::dynamic_pointer_cast<hcvc::OperatorApplication>(arguments[1])->operat0r()->name() == "[]") {
          std::dynamic_pointer_cast<hcvc::VariableConstant>(arguments[0])->variable()->set_is_data();
        }
        if(arguments[1]->kind() == hcvc::TermKind::Constant &&
           std::dynamic_pointer_cast<hcvc::Constant>(arguments[1])->is_variable_constant() &&
           arguments[0]->kind() == hcvc::TermKind::OpApp &&
           std::dynamic_pointer_cast<hcvc::OperatorApplication>(arguments[0])->operat0r()->name() == "[]") {
          std::dynamic_pointer_cast<hcvc::VariableConstant>(arguments[1])->variable()->set_is_data();
        }
        if(expr->getOpcodeStr().str() == "==") {
          op_name = "=";
        } else if(expr->getOpcodeStr().str() == "&&") {
          op_name = "and";
        } else if(expr->getOpcodeStr().str() == "||") {
          op_name = "or";
        } else if(expr->getOpcodeStr().str() == "!=") {
          auto arg = _context.apply("=", arguments);
          arguments.clear();
          arguments.push_back(arg);
          op_name = "not";
        } else if(expr->getOpcodeStr().str() == "%") {
          op_name = "mod";
        } else {
          op_name = expr->getOpcodeStr().str();
        }
        return _context.apply(op_name, arguments);
      }
    }

    hcvc::Expr compile(clang::CallExpr *expr, hcvc::Function *function = nullptr) {
      auto callee = expr->getDirectCallee();
      if(callee == nullptr) {
        std::cout << "Error: Indirect function calls are not supported." << std::endl;
        exit(1);
      }
      auto callee_name = callee->getName();
      if(callee_name == "assert_exp" || callee_name == "assume_exp") {
        if(expr->getNumArgs() > 0) {
          auto arg = expr->getArg(0)->IgnoreImplicit();
          if(auto str_literal = clang::dyn_cast<clang::StringLiteral>(arg)) {
            std::string str = str_literal->getString().str();
            auto frml = SpecParser(str, &this->scope(), _context).parse();
            if(callee_name == "assert_exp") {
              this->assure(frml, hcvc::Weakness::assertion_violation);
            }
            this->assume(frml);
            return _context.get_false();
          }
        }
        std::cout << "Error: " << callee_name.str() << " expects a string literal argument." << std::endl;
        exit(1);
      }
      std::vector<hcvc::Expr> arguments;
      for(auto arg: expr->arguments()) {
        auto compiled = compile(arg, function);
        arguments.push_back(compiled);
        if(compiled->type()->is_array()) {
          if(compiled->kind() == hcvc::TermKind::Constant) {
            auto cnst = std::dynamic_pointer_cast<hcvc::Constant>(compiled);
            if(cnst->is_variable_constant()) {
              auto var_cnst = std::dynamic_pointer_cast<hcvc::VariableConstant>(compiled);
              arguments.push_back(this->scope().get(var_cnst->variable()->size_variable()));
            }
          }
        }
      }
      if(callee->getName() == "assert") {
        // emit clauses (assertion violated)
        this->assure(arguments[0], hcvc::Weakness::assertion_violation);
        this->assume(arguments[0]);
      } else if(callee->getName() == "assume") {
        this->assume(arguments[0]);
      } else if(callee->getName() == "_exists") {
        // TODO: the problem with this is variable declaration
        std::vector<hcvc::Expr> vars;
        for(unsigned int k = 0; k < arguments.size() - 1; k++) {
          vars.push_back(arguments[k]);
        }
        return hcvc::QuantifiedFormula::create(hcvc::Quantifier::Exists, vars, arguments[arguments.size() - 1],
                                               _context);
      } else if(callee->getName() == "_forall") {
        // TODO: the problem with this is variable declaration
        std::vector<hcvc::Expr> vars;
        for(unsigned int k = 0; k < arguments.size() - 1; k++) {
          vars.push_back(arguments[k]);
        }
        return hcvc::QuantifiedFormula::create(hcvc::Quantifier::ForAll, vars, arguments[arguments.size() - 1],
                                               _context);
      } else if(callee->getName() == "_implies") {
        return _context.apply("=>", arguments);
      } else if(callee->getName() == "_return") {
        return hcvc::VariableConstant::create(function->return_variable(), 0, _context);
      } else {
        auto function = _module.get_function(callee->getName().str());
        // emit clauses (input satisfies function precondition)
        this->then(function->precondition_pred(), arguments);
        // add pre to the clause
        this->assume(function->precondition_pred(), arguments);
        // TODO: should not say that the modified parameter and their original have the same size
        hcvc::Expr returned_value;
        if(function->return_variable() != nullptr) {
          returned_value = hcvc::Constant::create("!rtrnd" + std::to_string(_ret_counter++),
                                                  function->return_type(),
                                                  _context);
          arguments.push_back(returned_value);
        }
        for(unsigned long i = 0, sizei = function->parameters().size(); i < sizei; i++) {
          if(function->parameters()[i]->is_modified()) {
            // retrieve the variable that was passed to this modified parameter
            auto input = arguments[i];
            if(input->kind() == hcvc::TermKind::Constant) {
              auto cnst = std::dynamic_pointer_cast<hcvc::Constant>(input);
              if(cnst->is_variable_constant()) {
                auto var_cnst = std::dynamic_pointer_cast<hcvc::VariableConstant>(input);
                auto variable = (hcvc::Variable *) var_cnst->variable();
                auto next = std::dynamic_pointer_cast<hcvc::VariableConstant>(
                    this->scope().get(variable))->next();
                this->scope().set(variable, next);
                arguments.push_back(next);
              } else {
                std::cout << "IMPL-UNREACH" << "\n";
                exit(10);
              }
            } else {
              std::cout << "IMPL-UNREACH" << "\n";
              exit(10);
            }
          }
        }
        this->assume(function->summary_pred(), arguments);
        if(function->return_variable() != nullptr) {
          return returned_value;
        } else {
          return _context.get_true();
        }
      }
      return _context.get_false();
    }

    hcvc::Expr compile(clang::DeclRefExpr *expr, hcvc::Function *function = nullptr) {
      auto var_name = expr->getDecl()->getNameAsString();
      if(var_name == "false") {
        return _context.get_false();
      } else if(var_name == "true") {
        return _context.get_true();
      } else {
        auto variable = this->scope().get_variable_by_name(var_name);
        return this->scope().get(variable);
      }
    }

    hcvc::Expr compile(clang::ImplicitCastExpr *expr, hcvc::Function *function = nullptr) {
      return compile(expr->getSubExprAsWritten(), function);
    }

    hcvc::Expr compile(clang::IntegerLiteral *expr, hcvc::Function *function = nullptr) {
      return hcvc::IntegerLiteral::get(llvm::toString(expr->getValue(), 10, true),
                                       compile_type(expr->getType(), _context), _context);
    }

    hcvc::Expr compile(clang::ParenExpr *expr, hcvc::Function *function = nullptr) {
      return compile(expr->getSubExpr(), function);
    }

    hcvc::Expr compile(clang::UnaryOperator *expr, hcvc::Function *function = nullptr) {
      if(expr->getOpcode() == clang::UnaryOperatorKind::UO_LNot) {
        return !compile(expr->getSubExpr(), function);
      } else if(expr->getOpcode() == clang::UnaryOperatorKind::UO_PostInc) {
        // get assigned variable name
        auto var_name = ((clang::DeclRefExpr *) expr->getSubExpr())->getDecl()->getNameAsString();
        // get variable in the scope with that name
        auto variable = this->scope().get_variable_by_name(var_name);
        // compute the next constant for that variable
        auto previous = this->scope().get(variable);
        auto next = std::dynamic_pointer_cast<hcvc::VariableConstant>(this->scope().get(variable))->next();
        // assign new_const to that variable
        this->scope().set(variable, next);
        this->assume(next == previous + hcvc::IntegerLiteral::get("1", next->type(), _context));
        return previous;
      } else if(expr->getOpcode() == clang::UnaryOperatorKind::UO_PostDec) {
        // get assigned variable name
        auto var_name = ((clang::DeclRefExpr *) expr->getSubExpr())->getDecl()->getNameAsString();
        // get variable in the scope with that name
        auto variable = this->scope().get_variable_by_name(var_name);
        // compute the next constant for that variable
        auto previous = this->scope().get(variable);
        auto next = std::dynamic_pointer_cast<hcvc::VariableConstant>(this->scope().get(variable))->next();
        // assign new_const to that variable
        this->scope().set(variable, next);
        this->assume(next == previous - hcvc::IntegerLiteral::get("1", next->type(), _context));
        return previous;
      } else if(expr->getOpcode() == clang::UnaryOperatorKind::UO_Minus) {
        return -compile(expr->getSubExpr(), function);
      } else if(expr->getOpcode() == clang::UnaryOperatorKind::UO_PreInc) {
        // get assigned variable name
        auto var_name = ((clang::DeclRefExpr *) expr->getSubExpr())->getDecl()->getNameAsString();
        // get variable in the scope with that name
        auto variable = this->scope().get_variable_by_name(var_name);
        // compute the next constant for that variable
        auto previous = this->scope().get(variable);
        auto next = std::dynamic_pointer_cast<hcvc::VariableConstant>(this->scope().get(variable))->next();
        // assign new_const to that variable
        this->scope().set(variable, next);
        this->assume(next == previous + hcvc::IntegerLiteral::get("1", next->type(), _context));
        return next;
      } else if(expr->getOpcode() == clang::UnaryOperatorKind::UO_PreDec) {
        // get assigned variable name
        auto var_name = ((clang::DeclRefExpr *) expr->getSubExpr())->getDecl()->getNameAsString();
        // get variable in the scope with that name
        auto variable = this->scope().get_variable_by_name(var_name);
        // compute the next constant for that variable
        auto previous = this->scope().get(variable);
        auto next = std::dynamic_pointer_cast<hcvc::VariableConstant>(this->scope().get(variable))->next();
        // assign new_const to that variable
        this->scope().set(variable, next);
        this->assume(next == previous - hcvc::IntegerLiteral::get("1", next->type(), _context));
        return next;
      } else {
        std::cout << "IMPL-MISSING" << "\n";
        exit(10);
      }
      return _context.get_false(); // case not handled
    }

  private:
    hcvc::Module &_module;
    hcvc::Context &_context;
    std::vector<hcvc::Expr> _pred_apps;
    std::vector<hcvc::Expr> _phi;
    std::stack<InvariantPredicate *> _loop_invariant_stack;
    Scope _scope;
  };

  class MultiStateCompiler {
  public:
    MultiStateCompiler(hcvc::Module &module, hcvc::Context &context, std::vector<State *> states)
        : _context(context), _module(module), _states(std::move(states)) {}

    void compile(clang::Stmt *stmt, hcvc::Function *function) {
      if(stmt == nullptr) {
        return;
      }
      for(auto state: _states) {
        if(stmt->getStmtClass() == clang::Stmt::CompoundStmtClass) {
          state->compile((clang::CompoundStmt *) stmt, function);
        } else if(stmt->getStmtClass() == clang::Stmt::DeclStmtClass) {
          state->compile((clang::DeclStmt *) stmt, function);
        } else if(stmt->getStmtClass() == clang::Stmt::IfStmtClass) {
          state->compile((clang::IfStmt *) stmt, function);
        } else if(stmt->getStmtClass() == clang::Stmt::ReturnStmtClass) {
          state->compile((clang::ReturnStmt *) stmt, function);
        } else if(stmt->getStmtClass() == clang::Stmt::WhileStmtClass) {
          state->compile((clang::WhileStmt *) stmt, function);
        } else { // expression statement
          // TODO: this else may take other stuff other than Expression Statement; add other cases
          auto expr = clang::dyn_cast<clang::Expr>(stmt);
          if(expr == nullptr) {
            stmt->dump();
            std::cout << "IMPL-MISSING in MultiStateCompiler: Unhandled statement type." << std::endl;
            exit(10);
          }
          state->compile(expr, function);
        }
      }
    }

  private:
    hcvc::Module &_module;
    hcvc::Context &_context;
    std::vector<State *> _states;
  };

  //*-- Compiler
  class Compiler {
  public:
    Compiler(clang::ASTContext *ast_context, clang::TranslationUnitDecl *translation_unit, hcvc::Context &context)
        : _ast_context(ast_context),
          _ast(translation_unit),
          _context(context), _module(new hcvc::Module(context)) {}

    hcvc::Module *compile() {
      // compile and initialize the function's declarations
      std::vector<clang::FunctionDecl *> functions;
      for(auto decl: _ast->decls()) {
        if(!decl->getLocation().isInvalid()) { // skip declarations with invalid location
          if(decl->getKind() == clang::Decl::Kind::Function) {
            auto *function = (clang::FunctionDecl *) decl;
            if(function->isImplicit()) continue; // skip implicit function declarations
            // skip the declarations of _requires and _ensures
            if(function->getNameAsString() == "_requires" || function->getNameAsString() == "_ensures") {
              continue;
            }
            // create the function
            std::vector<hcvc::Parameter *> parameters;
            auto modified_parameters = _modified_parameters(function); // get modified parameters of the function
            for(auto &parameter: function->parameters()) {
              // TODO: do we simplify by eliminating non used parameter
              // TODO: a static method to create parameter
              auto param = new hcvc::Parameter(parameter->getNameAsString(),
                                               compile_type(parameter->getType(), _context),
                                               modified_parameters.count(parameter) > 0,
                                               _context);
              if(param->type()->is_array()) {
                param->carry_size_variable();
              }
              parameters.push_back(param);
            }
            hcvc::Function::create(function->getNameAsString(),
                                   parameters,
                                   compile_type(function->getReturnType(), _context),
                                   _module);
            functions.push_back(function);
            // TODO: do we need to have a function dependency graph, could this not be be replaced by predicate dependency in the clauses
          }
        }
      }
      // compile each function
      for(const auto &function: functions) {
        if(function->getNameAsString() == "_requires" || function->getNameAsString() == "_ensures") {
          continue;
        }
        compile(function);
      }

      _module->hypergraph().simplify(_context);
      // return the populated module
      return _module;
    }

    void compile(clang::FunctionDecl *func_decl) {
      auto function = _module->get_function(func_decl->getNameAsString());
      // assert(function != nullptr);

      State state(*_module, _context);

      if(!function->parameters().empty()) {
        // create an old variable for each modified parameter
        std::vector<hcvc::Parameter *> declare_after;
        for(auto &parameter: function->parameters()) {
          if(parameter->is_modified()) {
            declare_after.push_back(parameter);
            state.scope().put(parameter->entry_value_holder());
          } else {
            state.scope().put(parameter);
          }
          if(parameter->type()->is_array()) {
            state.scope().put(parameter->size_variable());
          }
        }
        for(auto parameter: declare_after) { // this is just for aesthetic variable ordering
          state.scope().put(parameter);
        }

        // assign modified parameter to holder variables
        state.assume(function->precondition_pred());
        for(auto &parameter: function->parameters()) {
          if(parameter->is_modified()) {
            auto entry = state.scope().get(parameter->entry_value_holder());
            auto param = state.scope().get(parameter);
            state.assume(entry == param);
          }
        }
      }

      MultiStateCompiler sc(*_module, _context, {&state});
      sc.compile(func_decl->getBody(), function);

      // TODO: or if ... else that has returned
      if(((clang::CompoundStmt *) func_decl->getBody())->body_back()->getStmtClass() != clang::Stmt::ReturnStmtClass) {
        state.then(function->summary_pred());
      }
      return;
    }

  private:
    clang::ASTContext *_ast_context;
    clang::TranslationUnitDecl *_ast;
    hcvc::Context &_context;

    hcvc::Module *_module;

    /// Get the set of modified parameters of a function.
    static std::set<clang::ParmVarDecl *> _modified_parameters(clang::FunctionDecl *function) {
      //function->dump();
      std::set<clang::ParmVarDecl *> modified;
      std::stack<clang::Stmt *> stack;
      stack.push(function->getBody());
      while(!stack.empty()) {
        // pop from the stack
        auto elem = stack.top();
        stack.pop();
        if(elem == nullptr) continue;
        // check if it's an assignment
        if(elem->getStmtClass() == clang::Stmt::BinaryOperatorClass) {
          auto casted = (clang::BinaryOperator *) elem;
          if(casted->getOpcodeStr().str() == "=") { // TODO: other operator +=...
            if(casted->getLHS()->getStmtClass() == clang::Stmt::DeclRefExprClass) {
              auto lhs = (clang::DeclRefExpr *) casted->getLHS();
              modified.insert((clang::ParmVarDecl *) lhs->getDecl());
            } else if(casted->getLHS()->getStmtClass() == clang::Stmt::ArraySubscriptExprClass) {
              auto subscript = (clang::ArraySubscriptExpr *) casted->getLHS();
              auto decl = ((clang::DeclRefExpr *) ((clang::ImplicitCastExpr *) subscript->getBase())->getSubExpr())->getDecl();
              modified.insert((clang::ParmVarDecl *) decl);
            }
          }
        }
        // push children to the stack
        for(auto subelem: elem->children()) {
          stack.push(subelem);
        }
      }
      return modified;
    }
  };

}
