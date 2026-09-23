/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3KernelProjectionDecay
import ConnesWeilRH.Dev.C1SemilocalHardyTitchmarshUnitarityReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24RadialBoundaryPairTransport

/-!
# Translated Kernel Radial Tail Reduction to Riemann Hypothesis

This module unifies the two wings of the Sonin projection decay by reducing
the Fourier support projection of a translated kernel to the radial support
projection of its Hardy--Titchmarsh transform.

Key Theorems:
1. `sourceFourierSupportProjection_translation_norm_eq`:
   `‖sourceFourierSupportProjection lambda (cc20GlobalLogTranslation t k0)‖ =`
   `‖radialSupportProjection lambda`
   `  (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖`.
2. `sourceFourierSupportProjection_translation_normSq_eq`:
   Norm-squared version of the above identity.
3. `normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails`:
   Unifies the two wings: both the left wing ($t < -N$) and right wing ($t > N$)
   are controlled by the radial support projection on the translated vectors
   `cc20GlobalLogTranslation t k0` and
   `cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0)`.
4. `sourceCompressedRoot_squareSum_of_translated_radial_tails`:
   Discharges S3 survivor core square-summability from translated radial tails.
5. `riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq`:
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
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20YoshidaNearZeros
open Source.C1HealthyYoshidaDetector
open Source.C1SameOwnerWeil
open Source.C1G8AdjointShearGram
open Source.C1G8MasterExit
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

/-- Pointwise evaluation of the Fourier support projection through Hardy--Titchmarsh conjugation. -/
theorem sourceFourierSupportProjection_apply
    (lambda : CCM24SoninScale) (u : finiteSCarrier) :
    sourceFourierSupportProjection lambda u =
      archimedeanHardyTitchmarshOperator
        (radialSupportProjection lambda
          (archimedeanHardyTitchmarshOperator u)) := by
  rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation]
  rfl

/-- The Fourier support projection norm equals the radial projection norm of the Hardy transform. -/
theorem norm_sourceFourierSupportProjection
    (lambda : CCM24SoninScale) (u : finiteSCarrier) :
    ‖sourceFourierSupportProjection lambda u‖ =
      ‖radialSupportProjection lambda (archimedeanHardyTitchmarshOperator u)‖ := by
  rw [sourceFourierSupportProjection_apply]
  exact ccm24ArchimedeanHardyTitchmarsh.norm_map _

/-- Along a translated orbit, the Fourier support projection norm equals the radial
    support projection norm of the oppositely translated Hardy transform. -/
theorem sourceFourierSupportProjection_translation_norm_eq
    (lambda : CCM24SoninScale) (t : ℝ) (k0 : finiteSCarrier) :
    ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ =
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖ := by
  change ‖sourceFourierSupportProjection lambda (cc20GlobalLogTranslation t k0)‖ =
    ‖radialSupportProjection lambda
      (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖
  rw [norm_sourceFourierSupportProjection]
  have htrans := archimedeanHardyTitchmarsh_globalLogTranslation t k0
  change archimedeanHardyTitchmarshOperator (cc20GlobalLogTranslation t k0) =
    cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0) at htrans
  rw [htrans]

/-- Norm squared identity for the translated Fourier support projection. -/
theorem sourceFourierSupportProjection_translation_normSq_eq
    (lambda : CCM24SoninScale) (t : ℝ) (k0 : finiteSCarrier) :
    ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 =
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 := by
  rw [sourceFourierSupportProjection_translation_norm_eq]

/-- Sonin projection decay outside `[-N, N]` deduced from two radial tail decay bounds. -/
theorem normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails
    (lambda : CCM24SoninScale) (k0 : finiteSCarrier)
    (N : ℝ) (C : ℝ) (hN : 0 ≤ N)
    (hleft : ∀ t : ℝ, t < -N →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2)
    (hright : ∀ t : ℝ, N < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / t ^ 2) :
    ∀ t : ℝ, N < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
  have hright' : ∀ t : ℝ, N < t →
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
    intro t ht
    rw [sourceFourierSupportProjection_translation_normSq_eq]
    exact hright t ht
  exact normSq_sourceSoninCarrier_starProjection_le_of_wings lambda
    (cc20GlobalLogTranslation · k0) N C hN hleft hright'

/-- S3 Survivor Core square-summability deduced from translated radial tail bounds. -/
theorem sourceCompressedRoot_squareSum_of_translated_radial_tails
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
    (hleft : ∀ t : ℝ, t < -(N : ℝ) →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2)
    (hright : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / t ^ 2) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hdecay := normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails
    lambda k0 (N : ℝ) C hNpos.le hleft hright
  exact sourceCompressedRoot_squareSum_of_kernel_projection_decay
    owner lambda sourceBasis (cc20GlobalLogTranslation · k0) hcols N hN hNpos hC hdecay

/-- Master Exit to Mathlib RiemannHypothesis from translated radial tails and aggregate trace equality. -/
theorem riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq
    (hradial : ∀ rho : sourceNontrivialZeroSet,
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
          (∀ t : ℝ, t < -(N : ℝ) →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2) ∧
          (∀ t : ℝ, (N : ℝ) < t →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation (-t) (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / t ^ 2) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_kernel_wing_decay_and_aggregateEq
  intro rho hright
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, k0, N, hN, hNpos, C, hC,
    hdata, hcols, hleft, hright_rad, heq⟩ := hradial rho hright
  have hright_fourier : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ ^ 2 ≤ C / t ^ 2 := by
    intro t ht
    rw [sourceFourierSupportProjection_translation_normSq_eq]
    exact hright_rad t ht
  exact ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis,
    (cc20GlobalLogTranslation · k0), N, hN, hNpos, C, hC,
    hdata, hcols, hleft, hright_fourier, heq⟩

end Dev
end ConnesWeilRH
