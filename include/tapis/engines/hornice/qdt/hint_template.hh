#pragma once

#include "hcvc/logic/term.hh"
#include <iostream>
#include <memory>
#include "hcvc/program/variable.hh"
#include <vector>

namespace tapis::HornICE::qdt {

enum class VariableRole {
    UNKNOWN, INDEX, QUANTIFIER, ARRAY_SIZE, ARRAY, DATA, LITERAL
};

// A parameter in our template can be a simple expression (with its role)
// or a nested, complex expression (another HintTemplate).
struct TemplateParameter {
    hcvc::Expr expr;
    VariableRole role;
};

// The main recursive structure, updated to use TemplateParameter.
struct HintTemplate {
    const hcvc::Operator* op = nullptr;
    std::vector<TemplateParameter> simple_params;
    std::vector<std::shared_ptr<HintTemplate>> nested_params;
};

inline bool is_var_cnst(const hcvc::Expr &term) {
    if (term->kind() != hcvc::TermKind::Constant) return false;
    auto c = std::dynamic_pointer_cast<hcvc::Constant>(term);
    return c && c->is_variable_constant();
}

inline VariableRole get_variable_role(const hcvc::Variable* var) {
    if (var->type()->is_array()) return VariableRole::ARRAY;

    if (var->type()->is_int()) {
        // is_data() is the key property from your framework.
        if (!var->is_data()) {
            const auto& name = var->name();
            // Heuristics for special index types
            if (name.rfind("!k", 0) == 0) return VariableRole::QUANTIFIER;
            // if (name == "N") return VariableRole::ARRAY_SIZE; // Common convention
            return VariableRole::INDEX; // General index (like a loop counter)
        } else {
            return VariableRole::DATA; // Is an int but holds data (like 's' or synthetic vars)
        }
    }
    return VariableRole::UNKNOWN;
}
// The DECLARATION of our helper function
void print_hint_template(const std::shared_ptr<HintTemplate>& ht, int indent = 0);

}