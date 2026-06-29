/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20RHExit
import ConnesWeilRH.Source.ObjectDerivations

/-!
# CC20 source interface

This file names the CC20 inputs used for trace legality, normalization, and the
finite-vanishing RH exit criterion.
-/

namespace ConnesWeilRH
namespace Source

variable (A : ArchimedeanTraceSymbols)

def cc20ArchimedeanTraceSquare : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "378-387"
  manuscriptRole :=
    "archimedean support-square trace formula and traceequa"
  statement := ArchimedeanTraceSymbols.TraceSquareStatement A

def cc20TraceClassTemplate : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "448-464, 2106-2121"
  manuscriptRole :=
    "trace-class verification and quantized-calculus trace ideal template"
  statement := ArchimedeanTraceSymbols.TraceClassTemplateStatement A

def cc20OrdinaryTraceSupportSquare : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "378-387, 448-464, 2106-2121"
  manuscriptRole :=
    "ordinary positive trace and support-square trace are the same finite-lambda scalar"
  statement := ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A

def cc20MellinHalfDensityConvention : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "2014-2030"
  manuscriptRole :=
    "Mellin/Fourier half-density convention used in the RH exit"
  statement := ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement A

structure CC20FiniteVanishingRhExitData where
  rhDefinitionBridge : RHDefinitionBridge
  sourceFiniteVanishingCriterionPackage :
    SourceFiniteVanishingCriterionPackage rhDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge :=
      SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
        sourceFiniteVanishingCriterionPackage

structure CC20FiniteVanishingRhExitWitness where
  data : CC20FiniteVanishingRhExitData
  objectPackage_eq_sourcePackageConversion :
    data.cc20RHExitObjectPackage =
      SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
        data.sourceFiniteVanishingCriterionPackage

def CC20FiniteVanishingRhExitStatement : Prop :=
  ∃ data : CC20FiniteVanishingRhExitData,
    data.cc20RHExitObjectPackage =
      SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
        data.sourceFiniteVanishingCriterionPackage

def CC20FiniteVanishingRhExitWitness.ofSourcePackage
    {B : RHDefinitionBridge}
    (sourcePackage : SourceFiniteVanishingCriterionPackage B) :
    CC20FiniteVanishingRhExitWitness where
  data :=
    { rhDefinitionBridge := B
      sourceFiniteVanishingCriterionPackage := sourcePackage
      cc20RHExitObjectPackage :=
        SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
          sourcePackage }
  objectPackage_eq_sourcePackageConversion := rfl

theorem cc20_finite_vanishing_exit_witness_statement
    (witness : CC20FiniteVanishingRhExitWitness) :
    CC20FiniteVanishingRhExitStatement :=
  ⟨witness.data, witness.objectPackage_eq_sourcePackageConversion⟩

def cc20_finite_vanishing_exit_data_source_package
    (witness : CC20FiniteVanishingRhExitWitness) :
    SourceFiniteVanishingCriterionPackage
      witness.data.rhDefinitionBridge :=
  witness.data.sourceFiniteVanishingCriterionPackage

def cc20_finite_vanishing_exit_data_object_package
    (witness : CC20FiniteVanishingRhExitWitness) :
    CC20RHExitObjectPackage witness.data.rhDefinitionBridge :=
  witness.data.cc20RHExitObjectPackage

theorem cc20_finite_vanishing_exit_object_package_eq_source_conversion
    (witness : CC20FiniteVanishingRhExitWitness) :
    witness.data.cc20RHExitObjectPackage =
      SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
        witness.data.sourceFiniteVanishingCriterionPackage :=
  witness.objectPackage_eq_sourcePackageConversion

def cc20FiniteVanishingRhExit : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "2072-2085"
  manuscriptRole :=
    "finite-vanishing Weil positivity criterion implying source RH"
  statement := CC20FiniteVanishingRhExitStatement

def cc20SignsAndNormalizations : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "2131-2165"
  manuscriptRole :=
    "u_infty, qd u, and archimedean sign normalization"
  statement := ArchimedeanTraceSymbols.SignsAndNormalizationsStatement A

structure CC20Interface where
  archimedeanSymbols : ArchimedeanTraceSymbols
  archimedeanTraceSquare :
    (cc20ArchimedeanTraceSquare archimedeanSymbols).Holds
  traceClassTemplate : (cc20TraceClassTemplate archimedeanSymbols).Holds
  ordinaryTraceSupportSquare :
    (cc20OrdinaryTraceSupportSquare archimedeanSymbols).Holds
  mellinHalfDensityConvention :
    (cc20MellinHalfDensityConvention archimedeanSymbols).Holds
  rhDefinitionBridge : RHDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge
  signsAndNormalizations :
    (cc20SignsAndNormalizations archimedeanSymbols).Holds

namespace SourceObjectBackedCC20Interface

structure Data where
  sourceObjectPackage : SourceObject.SourceObjectPackage

def archimedeanSymbols (h : Data) : ArchimedeanTraceSymbols :=
  h.sourceObjectPackage.toArchimedeanTraceSymbols

def finiteVanishingRhExit (h : Data) :
    FiniteVanishingCriterionPackage :=
  h.sourceObjectPackage.toFiniteVanishingCriterionPackage

theorem archimedean_trace_square
    (h : Data) :
    (cc20ArchimedeanTraceSquare (archimedeanSymbols h)).Holds :=
  SourceObject.SourceObjectPackage.provesTraceSquareStatement
    h.sourceObjectPackage

theorem trace_class_template
    (h : Data) :
    (cc20TraceClassTemplate (archimedeanSymbols h)).Holds :=
  SourceObject.SourceObjectPackage.provesTraceClassTemplateStatement
    h.sourceObjectPackage

theorem ordinary_trace_support_square
    (h : Data) :
    (cc20OrdinaryTraceSupportSquare (archimedeanSymbols h)).Holds :=
  SourceObject.SourceObjectPackage.provesOrdinaryTraceSupportSquareStatement
    h.sourceObjectPackage

theorem mellin_half_density_convention
    (h : Data) :
    (cc20MellinHalfDensityConvention (archimedeanSymbols h)).Holds :=
  SourceObject.SourceObjectPackage.provesMellinHalfDensityConventionStatement
    h.sourceObjectPackage

theorem signs_and_normalizations
    (h : Data) :
    (cc20SignsAndNormalizations (archimedeanSymbols h)).Holds :=
  SourceObject.SourceObjectPackage.provesSignsAndNormalizationsStatement
    h.sourceObjectPackage

theorem finite_set_admissible
    (h : Data) :
    (finiteVanishingRhExit h).finiteSetAdmissible :=
  SourceObject.SourceObjectPackage.provesFiniteSetAdmissible
    h.sourceObjectPackage

theorem finite_vanishing_rh
    (h : Data)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RH :=
  SourceObject.SourceObjectPackage.provesFiniteVanishingCriterion
    h.sourceObjectPackage input htriple hpositive

theorem finite_vanishing_rh_factors_through_source_rh
    (h : Data)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    (finiteVanishingRhExit h).criterion input htriple hpositive =
      RHDefinitionBridge.source_rh_to_mathlib_rh
        h.sourceObjectPackage.cc20RHExit.rhDefinitionBridge
        (h.sourceObjectPackage.cc20RHExit.sourceCC20PropositionC1 input
          (h.sourceObjectPackage.cc20RHExit.tripleVanishingToMellinBridge
            input htriple)
          (h.sourceObjectPackage.cc20RHExit.qW_sign_bridge input
            (h.sourceObjectPackage.cc20RHExit.routeFullPositivityToQWNonnegative
              input hpositive))) :=
  SourceObject.SourceObjectPackage.finiteVanishingCriterion_factors_through_source_rh
    h.sourceObjectPackage input htriple hpositive

end SourceObjectBackedCC20Interface

namespace CC20Interface

def ofSourceObjectPackage
    (pkg : SourceObject.SourceObjectPackage) : CC20Interface where
  archimedeanSymbols := pkg.toArchimedeanTraceSymbols
  archimedeanTraceSquare :=
    SourceObject.SourceObjectPackage.provesTraceSquareStatement pkg
  traceClassTemplate :=
    SourceObject.SourceObjectPackage.provesTraceClassTemplateStatement pkg
  ordinaryTraceSupportSquare :=
    SourceObject.SourceObjectPackage.provesOrdinaryTraceSupportSquareStatement
      pkg
  mellinHalfDensityConvention :=
    SourceObject.SourceObjectPackage.provesMellinHalfDensityConventionStatement
      pkg
  rhDefinitionBridge := pkg.cc20RHExit.rhDefinitionBridge
  cc20RHExitObjectPackage :=
    SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
      pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage
  signsAndNormalizations :=
    SourceObject.SourceObjectPackage.provesSignsAndNormalizationsStatement pkg

def sourceFiniteVanishingRhExit (cc20 : CC20Interface) :
    SourceFiniteVanishingCriterionPackage cc20.rhDefinitionBridge :=
  SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
    cc20.cc20RHExitObjectPackage

def finiteVanishingRhExit (cc20 : CC20Interface) :
    FiniteVanishingCriterionPackage :=
  SourceFiniteVanishingCriterionPackage.toFiniteVanishingCriterionPackage
    (sourceFiniteVanishingRhExit cc20)

theorem finite_vanishing_source_rh
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    cc20.rhDefinitionBridge.SourceRH :=
  SourceFiniteVanishingCriterionPackage.criterion_source_output
    (sourceFiniteVanishingRhExit cc20) input htriple hpositive

theorem finite_vanishing_source_rh_of_c1_input_data
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData
        cc20.rhDefinitionBridge
        (sourceFiniteVanishingRhExit cc20).finiteVanishingSet input) :
    cc20.rhDefinitionBridge.SourceRH :=
  SourceFiniteVanishingCriterionPackage.criterion_source_output_of_c1_input_data
    (sourceFiniteVanishingRhExit cc20) input hdata

theorem finite_vanishing_mathlib_rh_point_of_c1_input_data
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData
        cc20.rhDefinitionBridge
        (sourceFiniteVanishingRhExit cc20).finiteVanishingSet input)
    (s : ℂ)
    (hzero : riemannZeta s = 0)
    (hnotNegEven : ¬∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    s.re = 1 / 2 :=
  SourceFiniteVanishingCriterionPackage.criterion_mathlib_rh_point_of_c1_input_data
    (sourceFiniteVanishingRhExit cc20) input hdata
    s hzero hnotNegEven hpole

theorem finite_vanishing_mathlib_rh_point
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity)
    (s : ℂ)
    (hzero : riemannZeta s = 0)
    (hnotNegEven : ¬∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    s.re = 1 / 2 :=
  SourceFiniteVanishingCriterionPackage.criterion_mathlib_rh_point
    (sourceFiniteVanishingRhExit cc20) input htriple hpositive
    s hzero hnotNegEven hpole

theorem finite_vanishing_mathlib_rh_statement_of_c1_input_data
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData
        cc20.rhDefinitionBridge
        (sourceFiniteVanishingRhExit cc20).finiteVanishingSet input) :
    RHDefinitionBridge.MathlibRHStatement :=
  SourceFiniteVanishingCriterionPackage.criterion_mathlib_rh_statement_of_c1_input_data
    (sourceFiniteVanishingRhExit cc20) input hdata

theorem finite_vanishing_mathlib_rh_statement
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RHDefinitionBridge.MathlibRHStatement :=
  SourceFiniteVanishingCriterionPackage.criterion_mathlib_rh_statement
    (sourceFiniteVanishingRhExit cc20) input htriple hpositive

theorem finite_vanishing_mathlib_rh_of_c1_input_data
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData
        cc20.rhDefinitionBridge
        (sourceFiniteVanishingRhExit cc20).finiteVanishingSet input) :
    _root_.RiemannHypothesis :=
  SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh_of_c1_input_data
    (sourceFiniteVanishingRhExit cc20) input hdata

theorem finite_vanishing_mathlib_rh
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis :=
  SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh
    (sourceFiniteVanishingRhExit cc20) input htriple hpositive

end CC20Interface

theorem finite_vanishing_rh_exit_holds
    (cc20 : CC20Interface) :
    cc20FiniteVanishingRhExit.Holds :=
  cc20_finite_vanishing_exit_witness_statement
    { data :=
        { rhDefinitionBridge := cc20.rhDefinitionBridge
          sourceFiniteVanishingCriterionPackage :=
            CC20Interface.sourceFiniteVanishingRhExit cc20
          cc20RHExitObjectPackage := cc20.cc20RHExitObjectPackage }
      objectPackage_eq_sourcePackageConversion := rfl }

end Source
end ConnesWeilRH
