/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

/-!
# Root-completed causal leg as a projection commutator

The centered causal crossing already removes the identity mass of the
normalized Euler inverse.  This module rewrites the remaining leg once more
as a genuine transport/projection commutator.  The identity is algebraic: it
uses only the quotient-band projection laws and does not assert a Schatten
bound or Gate 3U estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedCommutator

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSInverseMetric
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSTwoSidedRootRecombination

theorem sourceRootCompletedFiniteEulerCommonRightLeg_eq_projectionCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedCommonRightLeg owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (normalizedFiniteEulerInverse family)
          (sourceBandProjection lambda) ∘L
        sourceBandProjection lambda := by
  rw [sourceRootCompletedFiniteEulerCommonRightLeg_eq_centeredCausalCrossing]
  apply ContinuousLinearMap.ext
  intro u
  have hBsq :
      sourceBandProjection lambda
          (sourceBandProjection lambda u) = sourceBandProjection lambda u := by
    have h := DFunLike.congr_fun
      ((sourceBandProjection_isStarProjection lambda).isIdempotentElem) u
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using h
  have hPB :
      sourceSoninProjection lambda (sourceBandProjection lambda u) = 0 := by
    exact DFunLike.congr_fun
      (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda) u
  have hPBtransport :
      sourceSoninProjection lambda
          (sourceBandProjection lambda
            (normalizedFiniteEulerInverse family
              (sourceBandProjection lambda u))) = 0 := by
    exact DFunLike.congr_fun
      (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
      (normalizedFiniteEulerInverse family
        (sourceBandProjection lambda u))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,
    CCM24FiniteSTwoSidedRootRecombination.commutator,
    ContinuousLinearMap.mul_def, map_sub]
  rw [hBsq, hPB, hPBtransport, map_zero]

/-- The complete root-homogeneous first-jet owner consumes the commutator
form without separating either convolution root or either projection corner. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_projectionCommutatorPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
        rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (normalizedFiniteEulerInverse family)
          (sourceBandProjection lambda) ∘L
        sourceBandProjection lambda := by
  rw [sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair,
    sourceRootCompletedFiniteEulerCommonRightLeg_eq_projectionCommutator]

/-- The causal inverse/band commutator has an operator-norm bound independent
of the visible finite-prime family.  This is not a Hilbert--Schmidt bound. -/
theorem norm_normalizedFiniteEulerInverse_bandCommutator_le_two
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖CCM24FiniteSTwoSidedRootRecombination.commutator
        (normalizedFiniteEulerInverse family)
        (sourceBandProjection lambda)‖ ≤ 2 := by
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hBand : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  calc
    ‖normalizedFiniteEulerInverse family * sourceBandProjection lambda -
        sourceBandProjection lambda * normalizedFiniteEulerInverse family‖ ≤
      ‖normalizedFiniteEulerInverse family * sourceBandProjection lambda‖ +
        ‖sourceBandProjection lambda * normalizedFiniteEulerInverse family‖ :=
      norm_sub_le _ _
    _ ≤ (‖normalizedFiniteEulerInverse family‖ *
          ‖sourceBandProjection lambda‖) +
        (‖sourceBandProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * 1 + 1 * 1 := by gcongr
    _ = 2 := by norm_num

end CCM24FiniteSRootCompletedCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
