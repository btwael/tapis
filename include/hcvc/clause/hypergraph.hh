//
// Copyright (c) 2022 Wael-Amine Boutglay
//

#pragma once

#include <unordered_map>
#include "hcvc/clause/clause.hh"
#include "hcvc/clause/predicate.hh"
#include "hcvc/clause/set.hh"

namespace hcvc {
  class Module;
  class Function;
  class Variable;

  //*-- HyperGraph
  class HyperGraph: public ClauseSet {
  public:

    //*- methods

    void dump();

    inline void add_to_be_simplified(Predicate *predicate) {
      _to_be_simplified.insert(predicate);
    }

    void simplify(Context &context, Module* owner);

    // Move structs to public section for external access
    struct LinearCombinationLoop {
        // Existing fields from SubtractionLoop
        const Clause* inductive_clause;
        Predicate* loop_predicate;
        Function* owner_function;
        const Clause* entry_clause;
        const Clause* exit_clause;
        
        // NEW: Enhanced linear combination support
        struct LinearTerm {
            Expr coefficient;      // Could be constant (like IntegerLiteral) or expression
            Expr variable;         // The variable being accumulated
            bool is_positive;      // Sign of the term (for easy handling)
            
            LinearTerm(Expr coeff, Expr var, bool pos) 
                : coefficient(coeff), variable(var), is_positive(pos) {}
        };
        
        struct SumUpdate {
            const Variable* sum_var;        // The sum variable (s)
            long sum_var_arg_idx;          // Index in predicate parameters
            Expr sum_old_expr;             // s (old value)
            Expr sum_new_expr;             // s (new value) 
            std::vector<LinearTerm> terms; // All terms in the linear combination
            
            SumUpdate() : sum_var(nullptr), sum_var_arg_idx(-1) {}
        };
        
        std::vector<SumUpdate> sum_updates; // Support multiple sum variables
        
        LinearCombinationLoop() : inductive_clause(nullptr), loop_predicate(nullptr), 
                                 owner_function(nullptr), entry_clause(nullptr), exit_clause(nullptr) {}
    };
    
    struct SubtractionLoop {
      const Clause* entry_clause;
      const Clause* inductive_clause;
      const Clause* exit_clause;
      Predicate* loop_predicate;
      Function* owner_function;
      const Variable* sum_var;
      long sum_var_arg_idx = -1;
      Expr subtrahend_expr;
    };

  private:
    std::set<Predicate *> _to_be_simplified;

    std::vector<SubtractionLoop> find_subtraction_loops(Module* owner) const;
    void transform_subtraction_loops(Context &context, Module* owner);
    void transform_linear_combination_loops(Context &context, Module* owner);


    std::vector<LinearCombinationLoop> find_linear_combination_loops(Module* owner) const;
    void debug_print_linear_loops(const std::vector<LinearCombinationLoop>& loops) const;
  };

}