/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3AnnularKernelDiagonalBessel
import ConnesWeilRH.Dev.C1G8R3AnnularKernelPointwiseBound
import ConnesWeilRH.Dev.C1G8R3AnnularTailCosineRule

/-!
# Two-Sided Cosine Rule and Kernel Projection Decay to Riemann Hypothesis

This module establishes the two-sided cosine rule reduction and kernel projection
decay bridge for the S3 survivor core.

Key Theorems:
1. `sourceSoninCarrier_le_logRadialSupport`:
   The source Sonin carrier is contained in the log radial support submodule.
2. `sourceSoninCarrier_le_fourierSupport`:
   The source Sonin carrier is contained in the archimedean Fourier support submodule.
3. `norm_sourceSoninCarrier_starProjection_le_logRadialSupport` &
   `norm_sourceSoninCarrier_starProjection_le_fourierSupport`:
   The orthogonal projection onto the source Sonin carrier is bounded in norm by both
   the radial support projection and the Fourier support projection (two-sided cosine rule).
4. `normSq_sourceSoninCarrier_starProjection_le_of_wings`:
   Combines left-wing radial decay on `t < -N` and right-wing Fourier decay on `N < t`
   to prove uniform projection decay `‖K.starProjection (kernel t)‖^2 ≤ C / t^2` for all `|t| > N`.
5. `rootConvolution_tsum_le_of_inner_kernel_projection_decay`:
   Applies Bessel's identity to deduce the unwindowed root convolution decay:
   `∑' i, ‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i))) t‖ₑ ^ 2 ≤`
   `ENNReal.ofReal (C / t^2)`.
6. `sourceCompressedRoot_squareSum_of_kernel_wing_decay`:
   Discharges S3 survivor core square-summability from the two-sided wing estimates.
7. `riemannHypothesis_of_right_kernel_wing_decay_and_aggregateEq`:
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

noncomputable local instance logRadialSupportClosedSubspaceCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule :=
  (ccm24LogRadialSupportClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance archimedeanFourierSupportClosedSubspaceCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule :=
  (ccm24ArchimedeanFourierSupportClosedSubspace lambda).isClosed.completeSpace_coe

/-- The source Sonin carrier is contained in the log radial support submodule. -/
theorem sourceSoninCarrier_le_logRadialSupport (lambda : CCM24SoninScale) :
    (sourceSoninCarrier lambda) ≤ (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule := by
  intro u hu
  exact hu.1

/-- The source Sonin carrier is contained in the archimedean Fourier support submodule. -/
theorem sourceSoninCarrier_le_fourierSupport (lambda : CCM24SoninScale) :
    (sourceSoninCarrier lambda) ≤ (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule := by
  intro u hu
  exact hu.2

/-- Cosine rule: Sonin projection bounded by radial support projection. -/
theorem norm_sourceSoninCarrier_starProjection_le_logRadialSupport
    (lambda : CCM24SoninScale) (w : finiteSCarrier) :
    ‖(sourceSoninCarrier lambda).starProjection w‖ ≤
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection w‖ :=
  norm_starProjection_le_of_submodule_le (sourceSoninCarrier_le_logRadialSupport lambda) w

/-- Cosine rule: Sonin projection bounded by Fourier support projection. -/
theorem norm_sourceSoninCarrier_starProjection_le_fourierSupport
    (lambda : CCM24SoninScale) (w : finiteSCarrier) :
    ‖(sourceSoninCarrier lambda).starProjection w‖ ≤
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection w‖ :=
  norm_starProjection_le_of_submodule_le (sourceSoninCarrier_le_fourierSupport lambda) w

/-- Squared norm of Sonin projection bounded by radial projection squared norm. -/
theorem normSq_sourceSoninCarrier_starProjection_le_logRadialSupport
    (lambda : CCM24SoninScale) (w : finiteSCarrier) :
    ‖(sourceSoninCarrier lambda).starProjection w‖ ^ 2 ≤
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection w‖ ^ 2 := by
  have h := norm_sourceSoninCarrier_starProjection_le_logRadialSupport lambda w
  nlinarith [norm_nonneg ((sourceSoninCarrier lambda).starProjection w)]

/-- Squared norm of Sonin projection bounded by Fourier projection squared norm. -/
theorem normSq_sourceSoninCarrier_starProjection_le_fourierSupport
    (lambda : CCM24SoninScale) (w : finiteSCarrier) :
    ‖(sourceSoninCarrier lambda).starProjection w‖ ^ 2 ≤
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection w‖ ^ 2 := by
  have h := norm_sourceSoninCarrier_starProjection_le_fourierSupport lambda w
  nlinarith [norm_nonneg ((sourceSoninCarrier lambda).starProjection w)]

/-- Two-sided wing decay assembly: left-wing radial decay and right-wing Fourier decay
    imply uniform Sonin projection decay outside `[-N, N]`. -/
theorem normSq_sourceSoninCarrier_starProjection_le_of_wings
    (lambda : CCM24SoninScale) (kernel : ℝ → finiteSCarrier)
    (N : ℝ) (C : ℝ) (hN : 0 ≤ N)
    (hleft : ∀ t : ℝ, t < -N →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2)
    (hright : ∀ t : ℝ, N < t →
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) :
    ∀ t : ℝ, N < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2 := by
  intro t ht
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · have htlt : t < -N := by
      rw [abs_of_neg hneg] at ht
      linarith
    exact (normSq_sourceSoninCarrier_starProjection_le_logRadialSupport lambda (kernel t)).trans (hleft t htlt)
  · rw [abs_zero] at ht
    linarith
  · have htgt : N < t := by
      rw [abs_of_pos hpos] at ht
      exact ht
    exact (normSq_sourceSoninCarrier_starProjection_le_fourierSupport lambda (kernel t)).trans (hright t htgt)

private theorem enorm_rpow_two_eq_ofReal_pow_two (z : ℂ) :
    (‖z‖ₑ : ENNReal) ^ (2 : ℝ) = ENNReal.ofReal ‖z‖ ^ (2 : ℕ) := by
  rw [ENNReal.rpow_two, enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg z)]
  rfl

/-- Unwindowed root convolution decay deduced from kernel projection decay via Bessel identity. -/
theorem rootConvolution_tsum_le_of_inner_kernel_projection_decay
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (kernel : ℝ → finiteSCarrier)
    (hcols : ∀ i t,
      (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
        inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier) (kernel t))
    (N : ℕ) {C : ℝ}
    (hdecay : ∀ t : ℝ, (N : ℝ) < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) :
    ∀ t : ℝ, (N : ℝ) < |t| →
      (∑' i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C / t ^ 2) := by
  intro t ht
  have hconv : ∀ i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ) =
      ENNReal.ofReal (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖) ^ (2 : ℕ) := by
    intro i
    exact enorm_rpow_two_eq_ofReal_pow_two _
  have htsum : (∑' i, (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖ₑ : ENNReal) ^ (2 : ℝ)) =
      ∑' i, ENNReal.ofReal (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖) ^ (2 : ℕ) := by
    apply tsum_congr
    intro i
    exact hconv i
  rw [htsum]
  have hbessel := annular_kernelDiagonal_le_of_inner_kernel_projection_majorant
    (H := finiteSCarrier)
    (K := sourceSoninCarrier lambda)
    sourceBasis
    (cols := fun i s => (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) s)
    (kernel := kernel)
    (g := fun s => ‖(sourceSoninCarrier lambda).starProjection (kernel s)‖ ^ 2)
    hcols
    (fun s => le_rfl)
    t
  have hdecay_t := hdecay t ht
  calc
    ∑' i, ENNReal.ofReal (‖(rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t‖) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (‖(sourceSoninCarrier lambda).starProjection (kernel t)‖ ^ 2) := hbessel
    _ ≤ ENNReal.ofReal (C / t ^ 2) := ENNReal.ofReal_le_ofReal hdecay_t

/-- S3 Survivor Core square-summability deduced directly from kernel projection decay. -/
theorem sourceCompressedRoot_squareSum_of_kernel_projection_decay
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (kernel : ℝ → finiteSCarrier)
    (hcols : ∀ i t,
      (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
        inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier) (kernel t))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ t : ℝ, (N : ℝ) < |t| →
      ‖(sourceSoninCarrier lambda).starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hroot := rootConvolution_tsum_le_of_inner_kernel_projection_decay
    owner lambda sourceBasis kernel hcols N hdecay
  exact sourceCompressedRoot_squareSum_of_rootConvolution_decay
    owner lambda sourceBasis N hN hNpos hC hroot

/-- S3 Survivor Core square-summability deduced from two-sided cosine rule wing decay. -/
theorem sourceCompressedRoot_squareSum_of_kernel_wing_decay
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (kernel : ℝ → finiteSCarrier)
    (hcols : ∀ i t,
      (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
        inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier) (kernel t))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hleft : ∀ t : ℝ, t < -(N : ℝ) →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2)
    (hright : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hdecay := normSq_sourceSoninCarrier_starProjection_le_of_wings
    lambda kernel (N : ℝ) C hNpos.le hleft hright
  exact sourceCompressedRoot_squareSum_of_kernel_projection_decay
    owner lambda sourceBasis kernel hcols N hN hNpos hC hdecay

/-- Master Exit to Mathlib RiemannHypothesis from two-sided cosine rule wing decay
    and aggregate trace equality. -/
theorem riemannHypothesis_of_right_kernel_wing_decay_and_aggregateEq
    (hwing : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (kernel : ℝ → finiteSCarrier)
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (hNpos : 0 < (N : ℝ))
          (C : ℝ) (hC : 0 ≤ C),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (∀ i t,
            (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
              inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier) (kernel t)) ∧
          (∀ t : ℝ, t < -(N : ℝ) →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) ∧
          (∀ t : ℝ, (N : ℝ) < t →
            ‖(ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection (kernel t)‖ ^ 2 ≤ C / t ^ 2) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq
  intro rho hright
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, kernel, N, hN, hNpos, C, hC,
    hdata, hcols, hleft, hright_wing, heq⟩ := hwing rho hright
  have hdecay := normSq_sourceSoninCarrier_starProjection_le_of_wings
    lambda kernel (N : ℝ) C hNpos.le hleft hright_wing
  have hroot := rootConvolution_tsum_le_of_inner_kernel_projection_decay
    owner lambda sourceBasis kernel hcols N hdecay
  exact ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, hNpos, C, hC,
    hdata, hroot, heq⟩

end Dev
end ConnesWeilRH
