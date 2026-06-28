/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.RHDefinition

/-!
# CC20 finite-vanishing exit through a source RH bridge

This module separates the CC20 finite-vanishing criterion from the final
transport to Mathlib's `RiemannHypothesis`.  The analytic criterion should first
produce source RH for a specified `RHDefinitionBridge`; only then may the route
use the bridge to obtain Mathlib RH.
-/

namespace ConnesWeilRH
namespace Source

/--
A finite-vanishing criterion whose conclusion is source RH for a fixed
definition bridge.
-/
structure SourceFiniteVanishingCriterionPackage
    (B : RHDefinitionBridge) where
  finiteSetAdmissible : Prop
  sourceCriterion :
    ∀ input : WeilPositivityInput,
      input.tripleVanishing →
        input.fullWeilPositivity →
          B.SourceRH

def cc20TripleFiniteVanishingSet : Finset CriticalVanishingPoint :=
  {CriticalVanishingPoint.zero,
    CriticalVanishingPoint.half,
    CriticalVanishingPoint.one}

def RouteFiniteVanishingSetIsCC20Triple
    (F : Finset CriticalVanishingPoint) : Prop :=
  F = cc20TripleFiniteVanishingSet

def SourceFiniteSetAdmissibility
    (F : Finset CriticalVanishingPoint) : Prop :=
  CriticalVanishingPoint.zero ∈ F ∧
    CriticalVanishingPoint.half ∈ F ∧
      CriticalVanishingPoint.one ∈ F ∧
        RouteFiniteVanishingSetIsCC20Triple F

theorem cc20_triple_finite_set_is_triple :
    RouteFiniteVanishingSetIsCC20Triple cc20TripleFiniteVanishingSet := by
  rfl

theorem cc20_triple_finite_set_admissibility :
    SourceFiniteSetAdmissibility cc20TripleFiniteVanishingSet := by
  simp [SourceFiniteSetAdmissibility, RouteFiniteVanishingSetIsCC20Triple,
    cc20TripleFiniteVanishingSet]

def RouteTripleVanishingMatchesCC20Mellin
    (_F : Finset CriticalVanishingPoint) (input : WeilPositivityInput) : Prop :=
  input.tripleVanishing

def RouteFullPositivityMatchesCC20Nonpositivity
    (input : WeilPositivityInput) : Prop :=
  input.fullWeilPositivity

structure CC20PropositionC1InputData
    (F : Finset CriticalVanishingPoint)
    (input : WeilPositivityInput) where
  finiteSetIsTriple : RouteFiniteVanishingSetIsCC20Triple F
  tripleVanishingMatchesMellin :
    RouteTripleVanishingMatchesCC20Mellin F input
  fullPositivityMatchesNonpositivity :
    RouteFullPositivityMatchesCC20Nonpositivity input

def CC20PropositionC1SourceCriterion
    (B : RHDefinitionBridge) (F : Finset CriticalVanishingPoint)
    (input : WeilPositivityInput) : Prop :=
  CC20PropositionC1InputData F input → B.SourceRH

structure CC20RHExitObjectPackage
    (B : RHDefinitionBridge) where
  finiteVanishingSet : Finset CriticalVanishingPoint
  finiteSetAdmissible : SourceFiniteSetAdmissibility finiteVanishingSet
  propositionC1SourceCriterion :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1SourceCriterion B finiteVanishingSet input

theorem zero_mem_of_source_finite_set_admissibility
    {F : Finset CriticalVanishingPoint}
    (h : SourceFiniteSetAdmissibility F) :
    CriticalVanishingPoint.zero ∈ F :=
  h.1

theorem half_mem_of_source_finite_set_admissibility
    {F : Finset CriticalVanishingPoint}
    (h : SourceFiniteSetAdmissibility F) :
    CriticalVanishingPoint.half ∈ F :=
  h.2.1

theorem one_mem_of_source_finite_set_admissibility
    {F : Finset CriticalVanishingPoint}
    (h : SourceFiniteSetAdmissibility F) :
    CriticalVanishingPoint.one ∈ F :=
  h.2.2.1

theorem finite_set_is_triple_of_source_finite_set_admissibility
    {F : Finset CriticalVanishingPoint}
    (h : SourceFiniteSetAdmissibility F) :
    RouteFiniteVanishingSetIsCC20Triple F :=
  h.2.2.2

def cc20_proposition_c1_input_data
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (hfinite : SourceFiniteSetAdmissibility F)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    CC20PropositionC1InputData F input where
  finiteSetIsTriple :=
    finite_set_is_triple_of_source_finite_set_admissibility hfinite
  tripleVanishingMatchesMellin := htriple
  fullPositivityMatchesNonpositivity := hpositive

theorem triple_vanishing_of_c1_input_data
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData F input) :
    input.tripleVanishing :=
  h.tripleVanishingMatchesMellin

theorem full_positivity_of_c1_input_data
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData F input) :
    input.fullWeilPositivity :=
  h.fullPositivityMatchesNonpositivity

theorem finite_set_is_triple_of_c1_input_data
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData F input) :
    RouteFiniteVanishingSetIsCC20Triple F :=
  h.finiteSetIsTriple

namespace SourceFiniteVanishingCriterionPackage

def ofCC20RHExitObjectPackage
    {B : RHDefinitionBridge}
    (h : CC20RHExitObjectPackage B) :
    SourceFiniteVanishingCriterionPackage B where
  finiteSetAdmissible := SourceFiniteSetAdmissibility h.finiteVanishingSet
  sourceCriterion := by
    intro input htriple hpositive
    exact h.propositionC1SourceCriterion input
      (cc20_proposition_c1_input_data
        h.finiteSetAdmissible htriple hpositive)

def toFiniteVanishingCriterionPackage
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    FiniteVanishingCriterionPackage where
  finiteSetAdmissible := h.finiteSetAdmissible
  criterion := by
    intro input htriple hpositive
    exact RHDefinitionBridge.source_rh_to_mathlib_rh B
      (h.sourceCriterion input htriple hpositive)

theorem criterion_factors_through_source_rh
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    (toFiniteVanishingCriterionPackage h).criterion input htriple hpositive =
      RHDefinitionBridge.source_rh_to_mathlib_rh B
        (h.sourceCriterion input htriple hpositive) := by
  rfl

theorem criterion_source_output
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    B.SourceRH :=
  h.sourceCriterion input htriple hpositive

theorem criterion_mathlib_rh_point
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity)
    (s : ℂ)
    (hzero : riemannZeta s = 0)
    (hnotNegEven : ¬∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    s.re = 1 / 2 :=
  RHDefinitionBridge.mathlib_rh_point_of_source_rh B
    (criterion_source_output h input htriple hpositive)
    s hzero hnotNegEven hpole

theorem criterion_mathlib_rh_statement
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RHDefinitionBridge.MathlibRHStatement :=
  RHDefinitionBridge.source_rh_to_mathlib_rh_statement B
    (criterion_source_output h input htriple hpositive)

theorem criterion_to_mathlib_rh
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis :=
  RHDefinitionBridge.mathlib_rh_statement_iff_mathlib.1
    (criterion_mathlib_rh_statement h input htriple hpositive)

theorem standard_criterion_to_mathlib_rh
    (h : SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis :=
  criterion_to_mathlib_rh h input htriple hpositive

theorem standard_criterion_mathlib_rh_statement
    (h : SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RHDefinitionBridge.MathlibRHStatement :=
  criterion_mathlib_rh_statement h input htriple hpositive

theorem standard_criterion_mathlib_rh_point
    (h : SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity)
    (s : ℂ)
    (hzero : riemannZeta s = 0)
    (hnotNegEven : ¬∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    s.re = 1 / 2 :=
  criterion_mathlib_rh_point h input htriple hpositive
    s hzero hnotNegEven hpole

theorem standard_criterion_output_iff_mathlib
    (_h : SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard) :
    RHDefinitionBridge.standard.SourceRH ↔ _root_.RiemannHypothesis :=
  RHDefinitionBridge.standard_source_rh_iff_mathlib

end SourceFiniteVanishingCriterionPackage
end Source
end ConnesWeilRH
