/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorant
import ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantIntegral
import ConnesWeilRH.Dev.C1G8R3AnnularPointwiseReadback
import ConnesWeilRH.Dev.C1G8R3AnnularKernelDiagonalBessel

/-!
# Pointwise Annular Kernel Diagonal Bound

This module proves that the column energy of `sourceRootAnnularOutputWindow`
is pointwise majorized almost everywhere by `concreteWingMajorant N C`:
`∀ n ≥ N, ∀ᵐ t ∂volume, ∑' i, ‖(w_{N,n} e_i)(t)‖ₑ ^ 2 ≤ ENNReal.ofReal (g t)`.

Key Steps:
1. `indicator_enorm_sq`: The squared enorm of an indicator function is the indicator
   of the squared enorm.
2. `mem_annulus_imp_abs_gt`: Points in the annulus `Icc (-n) n \ Icc (-N) N` satisfy `N < |t|`.
3. `annulus_indicator_le_wing`: The annulus indicator is bounded pointwise by the
   outer wing function `if N < |t| then ... else 0`.
4. `sourceRootAnnularOutputWindow_tsum_le_concreteWingMajorant_of_root_decay`:
   Combines the annular indicator vanishing with the Bessel decay of the unwindowed
   root convolution to establish the almost-everywhere pointwise bound.
5. `sourceCompressedRoot_squareSum_of_rootConvolution_decay`:
   Discharges S3 survivor core square-summability directly from the unwindowed root decay.
6. `riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq`:
   Master exit to Mathlib `_root_.RiemannHypothesis`.

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
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20YoshidaNearZeros
open Source.C1HealthyYoshidaDetector
open Source.C1SameOwnerWeil
open Source.C1G8AdjointShearGram
open Source.C1G8MasterExit

/-- For any set `s` and function `f`, the squared enorm of `s.indicator f`
    equals `s.indicator (‖f ·‖ₑ ^ 2)`. -/
theorem indicator_enorm_sq {α : Type*} (s : Set α) (f : α → ℂ) (x : α) :
    (‖s.indicator f x‖ₑ : ENNReal) ^ (2 : ℝ) =
      s.indicator (fun y => (‖f y‖ₑ : ENNReal) ^ (2 : ℝ)) x := by
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- The annular difference set `Icc (-n) n \ Icc (-N) N` is contained in `{t | N < |t|}`. -/
theorem mem_annulus_imp_abs_gt {N n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)) :
    (N : ℝ) < |t| := by
  have hnot := ht.2
  rw [Set.mem_Icc, not_and_or] at hnot
  rcases hnot with h1 | h2
  · have hlt : t < -(N : ℝ) := lt_of_not_ge h1
    calc (N : ℝ) < -t := by linarith
      _ ≤ |t| := neg_le_abs t
  · have hgt : (N : ℝ) < t := lt_of_not_ge h2
    calc (N : ℝ) < t := hgt
      _ ≤ |t| := le_abs_self t

/-- Pointwise indicator domination: the annulus indicator is bounded by the wing majorant. -/
theorem annulus_indicator_le_wing {N n : ℕ} (t : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator (fun _ => ENNReal.ofReal v) t ≤
      if (N : ℝ) < |t| then ENNReal.ofReal v else 0 := by
  by_cases ht : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)
  · have habs := mem_annulus_imp_abs_gt ht
    rw [Set.indicator_of_mem ht, if_pos habs]
  · rw [Set.indicator_of_notMem ht]
    exact zero_le

/-- The pointwise decay of unwindowed root convolution implies the almost-everywhere
    pointwise domination of `sourceRootAnnularOutputWindow` by `concreteWingMajorant`. -/
theorem sourceRootAnnularOutputWindow_tsum_le_concreteWingMajorant_of_root_decay
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hroot : ∀ t : ℝ, (N : ℝ) < |t| →
      (∑' i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C / t ^ 2)) :
    ∀ n, N ≤ n → ∀ᵐ t ∂volume,
      (∑' i, (‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t) := by
  intro n hn
  -- For each basis vector, the output window agrees almost everywhere with the annulus indicator
  have hae : ∀ i : ι,
      (fun t => (‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) =ᵐ[volume]
      (fun t => (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
        (fun s => (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) s‖ₑ : ENNReal) ^ (2 : ℝ)) t) := by
    intro i
    have hcoe := sourceRootAnnularOutputWindow_coeFn_eq_annulus_indicator owner lambda N n hn (sourceBasis i)
    filter_upwards [hcoe] with t ht
    rw [ht, indicator_enorm_sq]
  -- Countable family of almost-everywhere equalities yields an almost-everywhere equality for the sum
  have hae_all : ∀ᵐ t ∂volume, ∀ i : ι,
      (‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ) =
      (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
        (fun s => (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) s‖ₑ : ENNReal) ^ (2 : ℝ)) t :=
    ae_all_iff.mpr hae
  filter_upwards [hae_all] with t ht
  have htsum : (∑' i, (‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) =
      ∑' i, (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
        (fun s => (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) s‖ₑ : ENNReal) ^ (2 : ℝ)) t :=
    tsum_congr ht
  rw [htsum]
  -- Now interchange the indicator and the tsum
  have hcomm : (∑' i, (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
      (fun s => (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) s‖ₑ : ENNReal) ^ (2 : ℝ)) t) =
      (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
      (fun s => ∑' i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) s‖ₑ : ENNReal) ^ (2 : ℝ)) t := by
    by_cases hmem : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)
    · simp [Set.indicator_of_mem hmem]
    · simp [Set.indicator_of_notMem hmem]
  rw [hcomm]
  -- Pointwise check depending on whether t is in the annulus
  by_cases hmem : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)
  · have habs := mem_annulus_imp_abs_gt hmem
    rw [Set.indicator_of_mem hmem]
    have hdecay := hroot t habs
    have hmajor : concreteWingMajorant (N : ℝ) C t = C / t ^ 2 := by
      unfold concreteWingMajorant
      rw [if_pos habs]
    rw [hmajor]
    exact hdecay
  · rw [Set.indicator_of_notMem hmem]
    have hnonneg : 0 ≤ concreteWingMajorant (N : ℝ) C t :=
      concreteWingMajorant_nonneg (N : ℝ) C hC t
    exact zero_le

/-- S3 Survivor Core square-summability deduced directly from root convolution decay. -/
theorem sourceCompressedRoot_squareSum_of_rootConvolution_decay
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hroot : ∀ t : ℝ, (N : ℝ) < |t| →
      (∑' i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C / t ^ 2)) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hpoint := sourceRootAnnularOutputWindow_tsum_le_concreteWingMajorant_of_root_decay
    owner lambda sourceBasis N hNpos hC hroot
  exact sourceCompressedRoot_squareSum_of_ae_pointwise_concreteWingMajorant
    owner lambda sourceBasis N hN hNpos hC hpoint

/-- Master Exit to Mathlib RiemannHypothesis from root convolution decay and aggregate trace equality. -/
theorem riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq
    (hroot : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (hNpos : 0 < (N : ℝ))
          (C : ℝ) (hC : 0 ≤ C),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (∀ t : ℝ, (N : ℝ) < |t| →
            (∑' i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) ≤
              ENNReal.ofReal (C / t ^ 2)) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_ae_pointwise_concrete_wing_majorant_and_aggregateEq
  intro rho hright
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, hNpos, C, hC,
    hdata, hdecay, heq⟩ := hroot rho hright
  have hpoint := sourceRootAnnularOutputWindow_tsum_le_concreteWingMajorant_of_root_decay
    owner lambda sourceBasis N hNpos hC hdecay
  exact ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, hNpos, C, hC,
    hdata, hpoint, heq⟩

end Dev
end ConnesWeilRH
