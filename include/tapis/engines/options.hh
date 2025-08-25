//
// Copyright (c) 2023 Wael-Amine Boutglay
//

#pragma once

#include <list>
#include <set>
#include <string>
#include "hcvc/logic/term.hh"
#include <optional>

namespace tapis {

  //*-- EngineKind
  enum class EngineKind {
    horn_ice_qdt, // The general Horn-ICE QDT
    c_to_smtlib
  };

  //*-- AbsIntDomain
  enum class AbsIntDomain {
    Box,
    Octagon,
    Polka
  };

  //*-- AttributeDomain
  enum class AttributeDomain {
    Empty, // emp
    Equality, // eq
    UpperBound, // ub
    StrictUpperBound, // sub
    Interval, // int
    DifferenceBound, // db
    Octagon, // oct
    Octahedron, // octh
    Polyhedra, // poly
    Kmod0, // k % c = 0 (c is an integer literal)
  };

  //*-- OutputMode
  enum class OutputMode {
    Default
  };

  //*-- Options
  class Options {
    class AbsIntOptions {
    public:
      bool perform = true; // perform abstract interpretation pre-analysis
      AbsIntDomain domain = AbsIntDomain::Octagon;
    };

    class ICEOptions {
      class ICETeacherOptions {
      public:
        bool multiple_counterexamples = false;
      };

      class ICELearnerOptions {
      public:
        std::set<AttributeDomain> index_domains = {AttributeDomain::Interval, AttributeDomain::DifferenceBound};
        std::set<AttributeDomain> data_domains = {AttributeDomain::Interval, AttributeDomain::DifferenceBound};
        bool attr_from_spec = true;
        bool attr_from_program = true;
        bool mix_data_indexes = false;
      };

      class QDTOptions {
      public:
        std::list<hcvc::Quantifier> quantification;
        unsigned long quantifier_numbers = 1;
        bool bounded_data_values = true;
        bool eq_classes_attr_vars = false;
        bool abstract_summary_input_arrays = true;
        std::list<std::set<std::string>> shared_quantifier_groups;
        std::optional<std::set<std::string>> use_sum_on_arrays;
        double hint_score_alpha = 0.85;

      };

    public:
      ICETeacherOptions teacher;
      ICELearnerOptions learner;
      QDTOptions qdt;
    };

    class OutputOptions {
    public:
      OutputMode mode = OutputMode::Default;
      bool statistics = false; // print statistics
    };

  public:
    AbsIntOptions absint;
    ICEOptions ice;
    OutputOptions output;

    EngineKind engine = EngineKind::horn_ice_qdt;
    bool chc_quantify_for_assert = true;
    bool print_invs = false;
    std::string path;
  };

  //*-- get_options()
  Options &get_options();

}
