/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.LinearAlgebra.Lagrange
import ConnesWeilRH.Source.CC20TestSpace

/-!
# Yoshida detector criterion

The theorem in this file proves the formal contradiction step from a detector
existence theorem and the CC20 finite-vanishing Weil criterion.  Detector
existence remains a separate concrete-test-space theorem; this module does not
store it as a field.
-/

namespace ConnesWeilRH
namespace Source

structure YoshidaDetector
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (rho : ℂ) where
  test : C.Test
  compactSupportSmooth : C.compactSupportSmooth test
  vanishesOnF : CC20VanishesOn C F test
  detectsRho : C.mellinAt test rho ≠ 0
  weilSumPositiveIfOffLine :
    RHDefinitionBridge.standard.sourceNontrivialZero rho →
      rho.re ≠ 1 / 2 →
        0 < C.weilLocalSum (C.starConvolution test)

def CC20YoshidaDetectorExists
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint) : Prop :=
  ∀ {rho : ℂ},
    RHDefinitionBridge.standard.sourceNontrivialZero rho →
      rho.re ≠ 1 / 2 →
        Nonempty (YoshidaDetector C F rho)

theorem standard_source_nontrivial_zero_ne_cc20_zero
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ criticalVanishingPointValue CriticalVanishingPoint.zero := by
  intro hzero
  have hz : riemannZeta (0 : ℂ) = 0 := by
    simpa [hzero, criticalVanishingPointValue] using
      RHDefinitionBridge.standard_mathlib_zeta_zero_of_source_nontrivial_zero
        rho hrho
  rw [riemannZeta_zero] at hz
  norm_num at hz

theorem standard_source_nontrivial_zero_ne_cc20_half_of_off_line
    {rho : ℂ}
    (hoff : rho.re ≠ 1 / 2) :
    rho ≠ criticalVanishingPointValue CriticalVanishingPoint.half := by
  intro hhalf
  apply hoff
  rw [hhalf, criticalVanishingPointValue]
  norm_num

theorem standard_source_nontrivial_zero_ne_cc20_one
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ criticalVanishingPointValue CriticalVanishingPoint.one := by
  intro hone
  exact
    RHDefinitionBridge.standard_mathlib_no_pole_of_source_nontrivial_zero
      rho hrho (by simpa [criticalVanishingPointValue] using hone)

theorem standard_source_nontrivial_zero_ne_cc20_triple_value_of_off_line
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (p : CriticalVanishingPoint) :
    rho ≠ criticalVanishingPointValue p := by
  cases p
  · exact standard_source_nontrivial_zero_ne_cc20_zero hrho
  · exact standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff
  · exact standard_source_nontrivial_zero_ne_cc20_one hrho

inductive CC20YoshidaInterpolationNode where
  | zero
  | half
  | one
  | rho
  deriving DecidableEq, Fintype

namespace CC20YoshidaInterpolationNode

noncomputable def nodeValue (z : ℂ) :
    CC20YoshidaInterpolationNode → ℂ
  | zero => criticalVanishingPointValue CriticalVanishingPoint.zero
  | half => criticalVanishingPointValue CriticalVanishingPoint.half
  | one => criticalVanishingPointValue CriticalVanishingPoint.one
  | rho => z

def desiredMellinValue :
    CC20YoshidaInterpolationNode → ℂ
  | zero => 0
  | half => 0
  | one => 0
  | rho => 1

noncomputable def interpolationPolynomial (rho : ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (nodeValue rho) desiredMellinValue

@[simp] theorem nodeValue_zero (rho : ℂ) :
    nodeValue rho zero =
      criticalVanishingPointValue CriticalVanishingPoint.zero := rfl

@[simp] theorem nodeValue_half (rho : ℂ) :
    nodeValue rho half =
      criticalVanishingPointValue CriticalVanishingPoint.half := rfl

@[simp] theorem nodeValue_one (rho : ℂ) :
    nodeValue rho one =
      criticalVanishingPointValue CriticalVanishingPoint.one := rfl

@[simp] theorem nodeValue_rho (z : ℂ) :
    nodeValue z .rho = z := rfl

@[simp] theorem desiredMellinValue_zero :
    desiredMellinValue zero = 0 := rfl

@[simp] theorem desiredMellinValue_half :
    desiredMellinValue half = 0 := rfl

@[simp] theorem desiredMellinValue_one :
    desiredMellinValue one = 0 := rfl

@[simp] theorem desiredMellinValue_rho :
    desiredMellinValue rho = 1 := rfl

theorem nodeValue_injective_of_standard_source_nontrivial_zero_off_line
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    Function.Injective (nodeValue rho) := by
  intro a b h
  cases a <;> cases b <;>
    simp [nodeValue, criticalVanishingPointValue] at h ⊢
  · exact (standard_source_nontrivial_zero_ne_cc20_zero hrho) h.symm
  · exact (standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff)
      (by simpa [criticalVanishingPointValue] using h.symm)
  · exact (standard_source_nontrivial_zero_ne_cc20_one hrho) h.symm
  · exact (standard_source_nontrivial_zero_ne_cc20_zero hrho) h
  · exact (standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff)
      (by simpa [criticalVanishingPointValue] using h)
  · exact (standard_source_nontrivial_zero_ne_cc20_one hrho) h

theorem interpolationPolynomial_eval_node
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (n : CC20YoshidaInterpolationNode) :
    Polynomial.eval (nodeValue rho n) (interpolationPolynomial rho) =
      desiredMellinValue n := by
  have hnodes : Set.InjOn (nodeValue rho) (Finset.univ : Finset CC20YoshidaInterpolationNode) :=
    fun _ _ _ _ h =>
      nodeValue_injective_of_standard_source_nontrivial_zero_off_line hrho hoff h
  simpa [interpolationPolynomial] using
    (Lagrange.eval_interpolate_at_node
      (r := desiredMellinValue)
      (v := nodeValue rho)
      (s := (Finset.univ : Finset CC20YoshidaInterpolationNode))
      (i := n)
      hnodes
      (by simp))

theorem interpolationPolynomial_eval_zero
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    Polynomial.eval
        (criticalVanishingPointValue CriticalVanishingPoint.zero)
        (interpolationPolynomial rho) = 0 := by
  simpa [nodeValue, desiredMellinValue] using
    interpolationPolynomial_eval_node hrho hoff zero

theorem interpolationPolynomial_eval_half
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    Polynomial.eval
        (criticalVanishingPointValue CriticalVanishingPoint.half)
        (interpolationPolynomial rho) = 0 := by
  simpa [nodeValue, desiredMellinValue] using
    interpolationPolynomial_eval_node hrho hoff half

theorem interpolationPolynomial_eval_one
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    Polynomial.eval
        (criticalVanishingPointValue CriticalVanishingPoint.one)
        (interpolationPolynomial rho) = 0 := by
  simpa [nodeValue, desiredMellinValue] using
    interpolationPolynomial_eval_node hrho hoff one

theorem interpolationPolynomial_eval_rho
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    Polynomial.eval rho (interpolationPolynomial rho) = 1 := by
  simpa [nodeValue, desiredMellinValue] using
    interpolationPolynomial_eval_node hrho hoff .rho

end CC20YoshidaInterpolationNode

theorem cc20_proposition_c1_from_yoshida_detector
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (_hfinite : SourceFiniteSetAdmissibility F)
    (_hdisjoint :
      SourceFiniteSetDisjointFromNontrivialZeros
        RHDefinitionBridge.standard F)
    (hexists : CC20YoshidaDetectorExists C F)
    (hcriterion : CC20FiniteVanishingWeilCriterion C F) :
    RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · simpa [RHDefinitionBridge.standard] using hline
  · rcases hexists hrho hline with ⟨D⟩
    have hnonpos : C.weilLocalSum (C.starConvolution D.test) ≤ 0 :=
      hcriterion D.test D.compactSupportSmooth D.vanishesOnF
    have hpos : 0 < C.weilLocalSum (C.starConvolution D.test) :=
      D.weilSumPositiveIfOffLine hrho hline
    exact False.elim ((not_lt_of_ge hnonpos) hpos)

end Source
end ConnesWeilRH
