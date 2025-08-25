//
// Copyright (c) 2025 Wael-Amine Boutglay
//

#pragma once

#include "attribute.hh"
#include "enumerator.hh"
#include "hcvc/logic/term.hh"
#include <map>
#include <memory>
#include <set>
#include <stack>
#include <variant>
#include <vector>
#include "tapis/engines/hornice/qdt/hint_template.hh"


namespace tapis::HornICE::qdt {

// Forward-declare the main class to be used in the HintTemplate struct
class NewAttributeSynthesizer;
struct HintTemplate;

// This visitor converts a canonicalized hcvc::Expr into our recursive HintTemplate structure.
class ExprToTemplateConverter : public hcvc::Visitor {
public:
    std::shared_ptr<HintTemplate> convert(const hcvc::Expr& expr);

private:
    // This using declaration must be private as it's an implementation detail
using ConversionResult = std::variant<TemplateParameter, std::shared_ptr<HintTemplate>>;
    std::stack<ConversionResult> _stack;
    std::set<hcvc::Expr> _quantified_vars_in_scope;

    // The visit methods are the implementation details, declared here as overridden virtual functions
    void visit(std::shared_ptr<hcvc::OperatorApplication> term) override;
    void visit(std::shared_ptr<hcvc::QuantifiedFormula> term) override;
    void visit(std::shared_ptr<hcvc::Constant> term) override;
    void visit(std::shared_ptr<hcvc::IntegerLiteral> term) override;
    void visit(std::shared_ptr<hcvc::BooleanLiteral> term) override;
    void visit(std::shared_ptr<hcvc::PredicateApplication> term) override;
    void visit(std::shared_ptr<hcvc::ArrayLiteral> term) override;
};

//*-- NewAttributeSynthesizer
class NewAttributeSynthesizer: public AttributeSynthesizer {
public:
    inline explicit NewAttributeSynthesizer(QuantifierManager& quantifier_manager, 
                                          AggregationManager& aggregation_manager)
      : _quantifier_manager(quantifier_manager),
        _aggregation_manager(aggregation_manager) {}

    ~NewAttributeSynthesizer() override;
    const std::set<std::shared_ptr<HintTemplate>>& get_hint_templates(const hcvc::Predicate* p) const override;
    //*- methods
    void set_predicate(const std::set<const hcvc::Predicate *> &predicates) override;
    void setup() override;
    std::pair<std::set<const Attribute *>, std::set<const Attribute *>>
    attributes(const hcvc::Predicate *predicate) const override;
    bool generate_attributes(DiagramPartialReachabilityGraph *sample) override;

private:
    std::set<const hcvc::Predicate *> _predicates;
    std::map<const hcvc::Predicate *, std::set<const Attribute *>> _init_index_attributes;
    std::map<const hcvc::Predicate *, std::set<const Attribute *>> _init_data_attributes;
    std::map<const hcvc::Predicate *, std::vector<Enumerator *>> _index_enumerators;
    std::map<const hcvc::Predicate *, std::vector<Enumerator *>> _data_enumerators;
    QuantifierManager &_quantifier_manager;
    AggregationManager& _aggregation_manager;
    std::map<const hcvc::Predicate*, std::set<std::shared_ptr<HintTemplate>>> _hint_templates;
};

}