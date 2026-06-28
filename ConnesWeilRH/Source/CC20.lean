/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20RHExit

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

def cc20MellinHalfDensityConvention : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "2014-2030"
  manuscriptRole :=
    "Mellin/Fourier half-density convention used in the RH exit"
  statement := ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement A

def cc20FiniteVanishingRhExit : SourceObligation where
  sourceKey := "CC20"
  sourceFile := "weil-compo.tex"
  lineRange := "2072-2085"
  manuscriptRole :=
    "finite-vanishing Weil positivity criterion implying source RH"
  statement :=
    ∃ B : RHDefinitionBridge, Nonempty (SourceFiniteVanishingCriterionPackage B)

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
  mellinHalfDensityConvention :
    (cc20MellinHalfDensityConvention archimedeanSymbols).Holds
  rhDefinitionBridge : RHDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge
  signsAndNormalizations :
    (cc20SignsAndNormalizations archimedeanSymbols).Holds

namespace CC20Interface

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

theorem finite_vanishing_mathlib_rh_statement
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RHDefinitionBridge.MathlibRHStatement :=
  SourceFiniteVanishingCriterionPackage.criterion_mathlib_rh_statement
    (sourceFiniteVanishingRhExit cc20) input htriple hpositive

theorem finite_vanishing_mathlib_rh
    (cc20 : CC20Interface)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis := by
  intro s hzero hnotNegEven hpole
  exact finite_vanishing_mathlib_rh_point
    cc20 input htriple hpositive s hzero hnotNegEven hpole

end CC20Interface

theorem finite_vanishing_rh_exit_holds
    (cc20 : CC20Interface) :
    cc20FiniteVanishingRhExit.Holds :=
  ⟨cc20.rhDefinitionBridge, ⟨CC20Interface.sourceFiniteVanishingRhExit cc20⟩⟩

end Source
end ConnesWeilRH
