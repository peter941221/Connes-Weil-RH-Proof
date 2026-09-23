/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecay

/-!
# Positive Radial Tail Reduction to Mathlib RiemannHypothesis

This module unifies the two wings of the Sonin projection decay by reformulating
both the left wing ($t < -N$) and the right wing ($t > N$) entirely as upper radial
support projection tails on the positive ray $(N, \infty)$.

Key Theorems:
1. `normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings`:
   Sonin projection decay from left-wing Fourier and right-wing radial estimates.
2. `normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails`:
   Decay outside `[-N, N]` from two positive-translation radial tails:
   - `k0` upper radial tail on `t > N`;
   - `Ht k0` upper radial tail on `s > N`.
3. `sourceCompressedRoot_squareSum_of_positive_radial_tails`:
   Discharges S3 survivor core square-summability from positive radial tails.
4. `normSq_sourceSoninCarrier_starProjection_le_of_vanishing_right_tail`:
   Specializes the right wing to identically vanishing compact support,
   leaving solely the Hardy tail obligation on `s > N`.
5. `riemannHypothesis_of_right_positive_radial_tails_and_aggregateEq`:
   Master exit to Mathlib `_root_.RiemannHypothesis` from positive radial tails.
6. `riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq`:
   Master exit where the right wing vanishes identically by compact support.

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

/-- Sonin projection decay outside `[-N, N]` deduced from left-wing Fourier and right-wing radial estimates. -/
theorem normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings
    (lambda : CCM24SoninScale) (kernel : ℝ → finiteSCarrier)
    (N : ℝ) (C : ℝ) (hN : 0 ≤ N)
    (hleft : ∀ t : ℝ, t < -N →
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2)
    (hright : ∀ t : ℝ, N < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) :
    ∀ t : ℝ, N < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2 := by
  intro t ht
  rcases lt_or_gt_of_ne (abs_ne_zero.mp (lt_of_le_of_lt hN ht).ne') with hneg | hpos
  · have hlt : t < -N := by
      rw [abs_of_neg hneg] at ht
      linarith
    have hle := normSq_sourceSoninCarrier_starProjection_le_fourierSupport lambda (kernel t)
    exact hle.trans (hleft t hlt)
  · have hgt : N < t := by
      rw [abs_of_pos hpos] at ht
      exact ht
    have hle := normSq_sourceSoninCarrier_starProjection_le_logRadialSupport lambda (kernel t)
    exact hle.trans (hright t hgt)

/-- Sonin projection decay outside `[-N, N]` deduced from two positive-translation radial tails:
    1. `k0` upper radial tail on `t > N`;
    2. `Ht k0` upper radial tail on `s > N`. -/
theorem normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails
    (lambda : CCM24SoninScale) (k0 : finiteSCarrier)
    (N : ℝ) (C : ℝ) (hN : 0 ≤ N)
    (hright : ∀ t : ℝ, N < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2)
    (hleft_ht : ∀ s : ℝ, N < s →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) :
    ∀ t : ℝ, N < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
  have hleft : ∀ t : ℝ, t < -N →
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
    intro t ht
    rw [sourceFourierSupportProjection_translation_normSq_eq]
    have hs : N < -t := by linarith
    have hbound := hleft_ht (-t) hs
    rw [neg_sq] at hbound
    exact hbound
  exact normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings
    lambda (cc20GlobalLogTranslation · k0) N C hN hleft hright

/-- Sonin projection decay when the right-wing radial projection vanishes identically
    (as for compactly supported tests), leaving solely the Hardy tail condition. -/
theorem normSq_sourceSoninCarrier_starProjection_le_of_vanishing_right_tail
    (lambda : CCM24SoninScale) (k0 : finiteSCarrier)
    (N : ℝ) (C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hvanish : ∀ t : ℝ, N < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ = 0)
    (hleft_ht : ∀ s : ℝ, N < s →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) :
    ∀ t : ℝ, N < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
  have hright : ∀ t : ℝ, N < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
    intro t ht
    rw [hvanish t ht, sq, mul_zero]
    exact div_nonneg hC (sq_nonneg t)
  exact normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails
    lambda k0 N C hN hright hleft_ht

/-- S3 Survivor Core square-summability deduced from positive-translation radial tails. -/
theorem sourceCompressedRoot_squareSum_of_positive_radial_tails
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (k0 : finiteSCarrier)
    (hcols : ∀ i t,
      (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
        inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier)
          (cc20GlobalLogTranslation t k0))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hright : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2)
    (hleft_ht : ∀ s : ℝ, (N : ℝ) < s →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hdecay := normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails
    lambda k0 (N : ℝ) C hNpos.le hright hleft_ht
  exact sourceCompressedRoot_squareSum_of_kernel_projection_decay
    owner lambda sourceBasis (cc20GlobalLogTranslation · k0) hcols N hN hNpos hC hdecay

/-- S3 Survivor Core square-summability when the right-wing radial projection vanishes identically. -/
theorem sourceCompressedRoot_squareSum_of_vanishing_right_tail
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (k0 : finiteSCarrier)
    (hcols : ∀ i t,
      (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
        inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier)
          (cc20GlobalLogTranslation t k0))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hvanish : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ = 0)
    (hleft_ht : ∀ s : ℝ, (N : ℝ) < s →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hdecay := normSq_sourceSoninCarrier_starProjection_le_of_vanishing_right_tail
    lambda k0 (N : ℝ) C hNpos.le hC hvanish hleft_ht
  exact sourceCompressedRoot_squareSum_of_kernel_projection_decay
    owner lambda sourceBasis (cc20GlobalLogTranslation · k0) hcols N hN hNpos hC hdecay

/-- Master Exit to Mathlib RiemannHypothesis from positive radial tails and aggregate trace equality. -/
theorem riemannHypothesis_of_right_positive_radial_tails_and_aggregateEq
    (hpos_radial : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (k0 : finiteSCarrier)
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (hNpos : 0 < (N : ℝ))
          (C : ℝ) (hC : 0 ≤ C),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (∀ i t,
            (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
              inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier)
                (cc20GlobalLogTranslation t k0)) ∧
          (∀ t : ℝ, (N : ℝ) < t →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2) ∧
          (∀ s : ℝ, (N : ℝ) < s →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq
  intro rho hright_zero
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, k0, N, hN, hNpos, C, hC,
    hdata, hcols, hright_rad, hleft_ht, heq⟩ := hpos_radial rho hright_zero
  have hdecay := normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails
    lambda k0 (N : ℝ) C hNpos.le hright_rad hleft_ht
  have hroot := rootConvolution_tsum_le_of_inner_kernel_projection_decay
    owner lambda sourceBasis (cc20GlobalLogTranslation · k0) hcols N hdecay
  exact ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, hNpos, C, hC,
    hdata, hroot, heq⟩

/-- Master Exit to Mathlib RiemannHypothesis where the right wing vanishes identically. -/
theorem riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq
    (hvanish_radial : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (k0 : finiteSCarrier)
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (hNpos : 0 < (N : ℝ))
          (C : ℝ) (hC : 0 ≤ C),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (∀ i t,
            (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
              inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier)
                (cc20GlobalLogTranslation t k0)) ∧
          (∀ t : ℝ, (N : ℝ) < t →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation t k0)‖ = 0) ∧
          (∀ s : ℝ, (N : ℝ) < s →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_positive_radial_tails_and_aggregateEq
  intro rho hzero
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, k0, N, hN, hNpos, C, hC,
    hdata, hcols, hvanish, hleft_ht, heq⟩ := hvanish_radial rho hzero
  have hright_rad : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
    intro t ht
    rw [hvanish t ht, sq, mul_zero]
    exact div_nonneg hC (sq_nonneg t)
  exact ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, k0, N, hN, hNpos, C, hC,
    hdata, hcols, hright_rad, hleft_ht, heq⟩

end Dev
end ConnesWeilRH
