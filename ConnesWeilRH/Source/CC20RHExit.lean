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

namespace SourceFiniteVanishingCriterionPackage

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

theorem criterion_to_mathlib_rh
    {B : RHDefinitionBridge}
    (h : SourceFiniteVanishingCriterionPackage B)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis := by
  intro s hzero hnotNegEven hpole
  exact criterion_mathlib_rh_point h input htriple hpositive
    s hzero hnotNegEven hpole

theorem standard_criterion_to_mathlib_rh
    (h : SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    _root_.RiemannHypothesis :=
  criterion_to_mathlib_rh h input htriple hpositive

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
