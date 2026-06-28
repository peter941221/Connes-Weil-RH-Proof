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

def cc20TripleFiniteVanishingSet : Finset CriticalVanishingPoint :=
  {CriticalVanishingPoint.zero,
    CriticalVanishingPoint.half,
    CriticalVanishingPoint.one}

noncomputable def criticalVanishingPointValue : CriticalVanishingPoint → ℂ
  | CriticalVanishingPoint.zero => 0
  | CriticalVanishingPoint.half => (1 / 2 : ℂ)
  | CriticalVanishingPoint.one => 1

def RouteFiniteVanishingSetIsCC20Triple
    (F : Finset CriticalVanishingPoint) : Prop :=
  F = cc20TripleFiniteVanishingSet

def SourceFiniteSetAdmissibility
    (F : Finset CriticalVanishingPoint) : Prop :=
  CriticalVanishingPoint.zero ∈ F ∧
    CriticalVanishingPoint.half ∈ F ∧
      CriticalVanishingPoint.one ∈ F ∧
        RouteFiniteVanishingSetIsCC20Triple F

def SourceFiniteSetDisjointFromNontrivialZeros
    (B : RHDefinitionBridge) (F : Finset CriticalVanishingPoint) : Prop :=
  ∀ p : CriticalVanishingPoint,
    p ∈ F → ¬B.sourceNontrivialZero (criticalVanishingPointValue p)

def SourceFiniteSetAdmissibilityForBridge
    (B : RHDefinitionBridge) (F : Finset CriticalVanishingPoint) : Prop :=
  SourceFiniteSetAdmissibility F ∧
    SourceFiniteSetDisjointFromNontrivialZeros B F

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
    (B : RHDefinitionBridge)
    (F : Finset CriticalVanishingPoint)
    (input : WeilPositivityInput) where
  finiteSetIsTriple : RouteFiniteVanishingSetIsCC20Triple F
  finiteSetDisjointFromNontrivialZeros :
    SourceFiniteSetDisjointFromNontrivialZeros B F
  tripleVanishingMatchesMellin :
    RouteTripleVanishingMatchesCC20Mellin F input
  fullPositivityMatchesNonpositivity :
    RouteFullPositivityMatchesCC20Nonpositivity input

def CC20PropositionC1SourceCriterion
    (B : RHDefinitionBridge) (F : Finset CriticalVanishingPoint)
    (input : WeilPositivityInput) : Prop :=
  CC20PropositionC1InputData B F input → B.SourceRH

structure CC20RHExitObjectPackage
    (B : RHDefinitionBridge) where
  finiteVanishingSet : Finset CriticalVanishingPoint
  finiteSetAdmissible : SourceFiniteSetAdmissibility finiteVanishingSet
  finiteSetDisjointFromNontrivialZeros :
    SourceFiniteSetDisjointFromNontrivialZeros B finiteVanishingSet
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

theorem finite_set_admissibility_of_bridge_admissibility
    {B : RHDefinitionBridge} {F : Finset CriticalVanishingPoint}
    (h : SourceFiniteSetAdmissibilityForBridge B F) :
    SourceFiniteSetAdmissibility F :=
  h.1

theorem finite_set_disjoint_of_bridge_admissibility
    {B : RHDefinitionBridge} {F : Finset CriticalVanishingPoint}
    (h : SourceFiniteSetAdmissibilityForBridge B F) :
    SourceFiniteSetDisjointFromNontrivialZeros B F :=
  h.2

theorem zero_not_source_nontrivial_zero_of_disjoint
    {B : RHDefinitionBridge} {F : Finset CriticalVanishingPoint}
    (hfinite : SourceFiniteSetAdmissibility F)
    (hdisjoint : SourceFiniteSetDisjointFromNontrivialZeros B F) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.zero) :=
  hdisjoint CriticalVanishingPoint.zero
    (zero_mem_of_source_finite_set_admissibility hfinite)

theorem half_not_source_nontrivial_zero_of_disjoint
    {B : RHDefinitionBridge} {F : Finset CriticalVanishingPoint}
    (hfinite : SourceFiniteSetAdmissibility F)
    (hdisjoint : SourceFiniteSetDisjointFromNontrivialZeros B F) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.half) :=
  hdisjoint CriticalVanishingPoint.half
    (half_mem_of_source_finite_set_admissibility hfinite)

theorem one_not_source_nontrivial_zero_of_disjoint
    {B : RHDefinitionBridge} {F : Finset CriticalVanishingPoint}
    (hfinite : SourceFiniteSetAdmissibility F)
    (hdisjoint : SourceFiniteSetDisjointFromNontrivialZeros B F) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.one) :=
  hdisjoint CriticalVanishingPoint.one
    (one_mem_of_source_finite_set_admissibility hfinite)

def cc20_proposition_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (hfinite : SourceFiniteSetAdmissibility F)
    (hdisjoint : SourceFiniteSetDisjointFromNontrivialZeros B F)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    CC20PropositionC1InputData B F input where
  finiteSetIsTriple :=
    finite_set_is_triple_of_source_finite_set_admissibility hfinite
  finiteSetDisjointFromNontrivialZeros := hdisjoint
  tripleVanishingMatchesMellin := htriple
  fullPositivityMatchesNonpositivity := hpositive

theorem triple_vanishing_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData B F input) :
    input.tripleVanishing :=
  h.tripleVanishingMatchesMellin

theorem full_positivity_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData B F input) :
    input.fullWeilPositivity :=
  h.fullPositivityMatchesNonpositivity

theorem finite_set_is_triple_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData B F input) :
    RouteFiniteVanishingSetIsCC20Triple F :=
  h.finiteSetIsTriple

theorem finite_set_disjoint_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (h : CC20PropositionC1InputData B F input) :
    SourceFiniteSetDisjointFromNontrivialZeros B F :=
  h.finiteSetDisjointFromNontrivialZeros

theorem zero_not_source_nontrivial_zero_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (hfinite : SourceFiniteSetAdmissibility F)
    (h : CC20PropositionC1InputData B F input) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.zero) :=
  zero_not_source_nontrivial_zero_of_disjoint hfinite
    (finite_set_disjoint_of_c1_input_data h)

theorem half_not_source_nontrivial_zero_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (hfinite : SourceFiniteSetAdmissibility F)
    (h : CC20PropositionC1InputData B F input) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.half) :=
  half_not_source_nontrivial_zero_of_disjoint hfinite
    (finite_set_disjoint_of_c1_input_data h)

theorem one_not_source_nontrivial_zero_of_c1_input_data
    {B : RHDefinitionBridge}
    {F : Finset CriticalVanishingPoint}
    {input : WeilPositivityInput}
    (hfinite : SourceFiniteSetAdmissibility F)
    (h : CC20PropositionC1InputData B F input) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.one) :=
  one_not_source_nontrivial_zero_of_disjoint hfinite
    (finite_set_disjoint_of_c1_input_data h)


/--
A finite-vanishing criterion whose conclusion is source RH for a fixed
definition bridge.
-/
structure SourceFiniteVanishingCriterionPackage
    (B : RHDefinitionBridge) where
  finiteSetAdmissible : Prop
  finiteVanishingSet : Finset CriticalVanishingPoint
  finiteSetAdmissibleData : SourceFiniteSetAdmissibility finiteVanishingSet
  finiteSetDisjointFromNontrivialZeros :
    SourceFiniteSetDisjointFromNontrivialZeros B finiteVanishingSet
  sourceCriterionData :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1InputData B finiteVanishingSet input →
        B.SourceRH

namespace SourceFiniteVanishingCriterionPackage

def ofCC20RHExitObjectPackage
    {B : RHDefinitionBridge}
    (h : CC20RHExitObjectPackage B) :
    SourceFiniteVanishingCriterionPackage B where
  finiteSetAdmissible := SourceFiniteSetAdmissibility h.finiteVanishingSet
  finiteVanishingSet := h.finiteVanishingSet
  finiteSetAdmissibleData := h.finiteSetAdmissible
  finiteSetDisjointFromNontrivialZeros :=
    h.finiteSetDisjointFromNontrivialZeros
  sourceCriterionData := by
    intro input hdata
    exact h.propositionC1SourceCriterion input hdata

def sourceCriterion
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
  B.SourceRH :=
  h.sourceCriterionData input
    (cc20_proposition_c1_input_data
      h.finiteSetAdmissibleData
      h.finiteSetDisjointFromNontrivialZeros htriple hpositive)

theorem source_criterion_data_output
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData B h.finiteVanishingSet input) :
    B.SourceRH :=
  h.sourceCriterionData input hdata

theorem source_criterion_uses_c1_input_data
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    h.sourceCriterion input htriple hpositive =
      h.sourceCriterionData input
        (cc20_proposition_c1_input_data
          h.finiteSetAdmissibleData
          h.finiteSetDisjointFromNontrivialZeros htriple hpositive) := by
  rfl

theorem finite_set_admissible_of_source_package
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    SourceFiniteSetAdmissibility h.finiteVanishingSet :=
  h.finiteSetAdmissibleData

theorem zero_mem_of_source_package_finite_set
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    CriticalVanishingPoint.zero ∈ h.finiteVanishingSet :=
  zero_mem_of_source_finite_set_admissibility h.finiteSetAdmissibleData

theorem half_mem_of_source_package_finite_set
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    CriticalVanishingPoint.half ∈ h.finiteVanishingSet :=
  half_mem_of_source_finite_set_admissibility h.finiteSetAdmissibleData

theorem one_mem_of_source_package_finite_set
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    CriticalVanishingPoint.one ∈ h.finiteVanishingSet :=
  one_mem_of_source_finite_set_admissibility h.finiteSetAdmissibleData

theorem finite_set_is_triple_of_source_package
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    RouteFiniteVanishingSetIsCC20Triple h.finiteVanishingSet :=
  finite_set_is_triple_of_source_finite_set_admissibility
    h.finiteSetAdmissibleData

theorem finite_set_disjoint_of_source_package
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    SourceFiniteSetDisjointFromNontrivialZeros B h.finiteVanishingSet :=
  h.finiteSetDisjointFromNontrivialZeros

theorem zero_not_source_nontrivial_zero_of_source_package
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.zero) :=
  zero_not_source_nontrivial_zero_of_disjoint
    h.finiteSetAdmissibleData h.finiteSetDisjointFromNontrivialZeros

theorem half_not_source_nontrivial_zero_of_source_package
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.half) :=
  half_not_source_nontrivial_zero_of_disjoint
    h.finiteSetAdmissibleData h.finiteSetDisjointFromNontrivialZeros

theorem one_not_source_nontrivial_zero_of_source_package
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    ¬B.sourceNontrivialZero
      (criticalVanishingPointValue CriticalVanishingPoint.one) :=
  one_not_source_nontrivial_zero_of_disjoint
    h.finiteSetAdmissibleData h.finiteSetDisjointFromNontrivialZeros

def toFiniteVanishingCriterionPackage
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B) :
    FiniteVanishingCriterionPackage where
  finiteSetAdmissible := SourceFiniteSetAdmissibility h.finiteVanishingSet
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

theorem criterion_source_output_of_c1_input_data
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData B h.finiteVanishingSet input) :
    B.SourceRH :=
  h.sourceCriterionData input hdata

theorem criterion_source_output_uses_c1_input_data
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    criterion_source_output h input htriple hpositive =
      criterion_source_output_of_c1_input_data h input
        (cc20_proposition_c1_input_data
          h.finiteSetAdmissibleData
          h.finiteSetDisjointFromNontrivialZeros htriple hpositive) := by
  rfl

theorem criterion_mathlib_rh_point_of_c1_input_data
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData B h.finiteVanishingSet input)
    (s : ℂ)
    (hzero : riemannZeta s = 0)
    (hnotNegEven : ¬∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    s.re = 1 / 2 :=
  RHDefinitionBridge.mathlib_rh_point_of_source_rh B
    (criterion_source_output_of_c1_input_data h input hdata)
    s hzero hnotNegEven hpole

theorem criterion_mathlib_rh_statement_of_c1_input_data
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData B h.finiteVanishingSet input) :
    RHDefinitionBridge.MathlibRHStatement :=
  RHDefinitionBridge.source_rh_to_mathlib_rh_statement B
    (criterion_source_output_of_c1_input_data h input hdata)

theorem criterion_to_mathlib_rh_of_c1_input_data
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (hdata :
      CC20PropositionC1InputData B h.finiteVanishingSet input) :
    _root_.RiemannHypothesis :=
  RHDefinitionBridge.mathlib_rh_statement_iff_mathlib.1
    (criterion_mathlib_rh_statement_of_c1_input_data h input hdata)

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
  criterion_mathlib_rh_point_of_c1_input_data h input
    (cc20_proposition_c1_input_data
      h.finiteSetAdmissibleData
      h.finiteSetDisjointFromNontrivialZeros htriple hpositive)
    s hzero hnotNegEven hpole

theorem criterion_mathlib_rh_statement
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RHDefinitionBridge.MathlibRHStatement :=
  criterion_mathlib_rh_statement_of_c1_input_data h input
    (cc20_proposition_c1_input_data
      h.finiteSetAdmissibleData
      h.finiteSetDisjointFromNontrivialZeros htriple hpositive)

theorem criterion_to_mathlib_rh
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis :=
  criterion_to_mathlib_rh_of_c1_input_data h input
    (cc20_proposition_c1_input_data
      h.finiteSetAdmissibleData
      h.finiteSetDisjointFromNontrivialZeros htriple hpositive)

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
