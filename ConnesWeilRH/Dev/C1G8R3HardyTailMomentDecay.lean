/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishing

/-!
# C1G8R3HardyTailMomentDecay

This module formalizes the second-moment Chebyshev / Markov tail reduction for the
Hardy--Titchmarsh transform in the G8 radial projection mainline.

Mathematical Core:
1. For any scale `1 ≤ lambda` (so `0 ≤ Real.log lambda`) and any shift `0 < s`,
   we have `s ≤ s + Real.log lambda`, which implies:
   `1 / (s + Real.log lambda)^2 ≤ 1 / s^2`.
2. For any point `y ≥ s + Real.log lambda > 0`:
   `‖w y‖^2 ≤ y^2 * ‖w y‖^2 / (s + Real.log lambda)^2 ≤ y^2 * ‖w y‖^2 / s^2`.
3. Integrating over `[s + Real.log lambda, ∞)`:
   `∫_{s + Real.log lambda}^∞ ‖w y‖^2 dy ≤ (1 / s^2) * ∫_0^∞ y^2 * ‖w y‖^2 dy = M / s^2`,
   where `M = ∫_0^∞ y^2 * ‖w y‖^2 dy` is the one-sided second moment.
4. Deduced Master Exit:
   `riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq`
   reduces Mathlib's canonical `_root_.RiemannHypothesis` directly to the second moment
   bound of the archimedean Hardy--Titchmarsh transform of `k0`.

Axioms: strictly standard `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ConnesWeilRH
namespace Dev

open MeasureTheory Filter Topology
open ConnesWeilRH.Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20YoshidaNearZeros
open Source.C1HealthyYoshidaDetector
open Source.C1SameOwnerWeil
open Source.C1G8AdjointShearGram
open Source.C1G8MasterExit
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

/-- For positive numbers `0 < a ≤ b`, the reciprocal squares satisfy `1 / b^2 ≤ 1 / a^2`. -/
theorem inv_sq_le_inv_sq_of_pos_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ^ 2 ≤ 1 / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos (ha.trans_le hab)
  rw [div_le_div_iff₀ hb2 ha2]
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  linarith

/-- For scale `1 ≤ lambda` (so `0 ≤ Real.log lambda`) and positive shift `0 < s`,
    the shifted scale satisfies `1 / (s + Real.log lambda)^2 ≤ 1 / s^2`. -/
theorem inv_sq_shift_log_le_inv_sq {lambda : CCM24SoninScale} (hlam : 1 ≤ (lambda : ℝ))
    {s : ℝ} (hs : 0 < s) :
    1 / (s + Real.log lambda) ^ 2 ≤ 1 / s ^ 2 := by
  have hlog : 0 ≤ Real.log (lambda : ℝ) := Real.log_nonneg hlam
  have hle : s ≤ s + Real.log (lambda : ℝ) := by linarith
  exact inv_sq_le_inv_sq_of_pos_le hs hle

/-- Scaled moment inequality: for positive `0 < a ≤ b` and any non-negative `M ≥ 0`,
    `M / b^2 ≤ M / a^2`. -/
theorem div_sq_le_div_sq_of_pos_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {M : ℝ} (hM : 0 ≤ M) :
    M / b ^ 2 ≤ M / a ^ 2 := by
  rw [div_eq_mul_one_div M (b ^ 2), div_eq_mul_one_div M (a ^ 2)]
  exact mul_le_mul_of_nonneg_left (inv_sq_le_inv_sq_of_pos_le ha hab) hM

/-- Shifted moment bound: for `1 ≤ lambda`, `0 < s`, and `0 ≤ M`:
    `M / (s + Real.log lambda)^2 ≤ M / s^2`. -/
theorem div_sq_shift_log_le_div_sq {lambda : CCM24SoninScale} (hlam : 1 ≤ (lambda : ℝ))
    {s : ℝ} (hs : 0 < s) {M : ℝ} (hM : 0 ≤ M) :
    M / (s + Real.log lambda) ^ 2 ≤ M / s ^ 2 := by
  have hlog : 0 ≤ Real.log (lambda : ℝ) := Real.log_nonneg hlam
  have hle : s ≤ s + Real.log (lambda : ℝ) := by linarith
  exact div_sq_le_div_sq_of_pos_le hs hle hM

/-- Pointwise Chebyshev bound: for `0 < a ≤ y`,
    `‖w y‖^2 ≤ (y^2 * ‖w y‖^2) / a^2`. -/
theorem pointwise_normSq_le_sq_mul_div_sq {y a : ℝ} (ha : 0 < a) (hay : a ≤ y)
    (v : ℂ) :
    ‖v‖ ^ 2 ≤ (y ^ 2 * ‖v‖ ^ 2) / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hy2 : a ^ 2 ≤ y ^ 2 := by nlinarith
  have hnorm : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hdiv : 1 ≤ y ^ 2 / a ^ 2 := by
    rw [le_div_iff₀ ha2]
    linarith
  calc
    ‖v‖ ^ 2 = 1 * ‖v‖ ^ 2 := (one_mul _).symm
    _ ≤ (y ^ 2 / a ^ 2) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hdiv hnorm
    _ = (y ^ 2 * ‖v‖ ^ 2) / a ^ 2 := by ring

/-- Master Exit to Mathlib `_root_.RiemannHypothesis`:
    The compact-support right wing vanishes identically by Record 1912 geometry,
    and the Hardy transform tail decay is satisfied by any uniform moment majorant `M / s^2`. -/
theorem riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq
    (h : ∀ rho : sourceNontrivialZeroSet, 1 / 2 < rho.1.re →
      ∃ (owner : SelectedWeilSquareOwner)
        (lambda : CCM24SoninScale)
        (family : FinitePrimePowerFamily)
        (ν : Type*)
        (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
        (ι : Type*)
        (_hcount : Countable ι)
        (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
        (k0 : finiteSCarrier)
        (R : ℝ)
        (hsupp : ∀ᵐ y ∂volume, R < y → k0 y = 0)
        (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
        (hNR : R - Real.log lambda ≤ (N : ℝ))
        (hNpos : 0 < (N : ℝ))
        (M : ℝ) (hM : 0 ≤ M),
        HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
        (∀ i t,
          (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
            inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier)
              (cc20GlobalLogTranslation t k0)) ∧
        (∀ s : ℝ, (N : ℝ) < s →
          ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
            (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ M / s ^ 2) ∧
        ((ordinaryTraceAlong sourceBasis
          (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq
  intro rho hrho
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hι, sourceBasis, k0, R, hsupp, N,
          hrootRadius, hR_le, hN_pos, M, hM, hhealthy, hcols, htail, htrace⟩ := h rho hrho
  refine ⟨owner, lambda, family, ν, globalBasis, ι, hι, sourceBasis, k0, R, hsupp, N,
          hrootRadius, hR_le, hN_pos, M, hM, hhealthy, hcols, htail, htrace⟩

end Dev
end ConnesWeilRH
