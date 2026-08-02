/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalDetectorNormalForm

/-!
# Signed pointwise diagonal for the physical Gate response

Proof 732 gives the detector-only source owner

```text
J^dagger W U_S + F_S^dagger W J.
```

Using `U_S = F_S + P_S`, this file identifies the forward conjugate pair and
the remaining complete physical-leakage crossing.  The forward pair is
self-adjoint and its diagonal is twice one real part.  All statements are at
operator or pointwise-diagonal level: the two pieces are not asserted to be
separately trace class, and no infinite trace is split.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalSignedDiagonal

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSGatePhysicalDetectorNormalForm
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The forward detector crossing together with its exact adjoint orientation. -/
noncomputable def sourceGatePhysicalForwardSymmetricResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceActualBandForwardCoframe lambda family +
    (sourceActualBandForwardCoframe lambda family)† ∘L
      detectorOperator owner ∘L sourceInclusion lambda

/-- The one complete physical-leakage detector crossing left after the
forward conjugate pair is removed. -/
noncomputable def sourceGatePhysicalLeakageCrossingResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
    sourcePhysicalCoframeLeakage lambda family

/-- Operator-level decomposition of the detector off-diagonal owner.  This
identity does not assert separate trace legality for its two summands. -/
theorem sourceGatePhysicalDetectorOffDiagonalResponse_eq_forward_add_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGatePhysicalDetectorOffDiagonalResponse owner lambda family =
      sourceGatePhysicalForwardSymmetricResponse owner lambda family +
        sourceGatePhysicalLeakageCrossingResponse owner lambda family := by
  rw [sourceGatePhysicalDetectorOffDiagonalResponse,
    sourceGatePhysicalForwardSymmetricResponse,
    sourceGatePhysicalLeakageCrossingResponse,
    sourceEndpointCancellationResidual_eq_forward_add_physicalLeakage]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]
  abel

/-- The complete forward pair is self-adjoint. -/
theorem sourceGatePhysicalForwardSymmetricResponse_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceGatePhysicalForwardSymmetricResponse owner lambda family)† =
      sourceGatePhysicalForwardSymmetricResponse owner lambda family := by
  rw [sourceGatePhysicalForwardSymmetricResponse,
    ContinuousLinearMap.adjoint.map_add]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq,
    ContinuousLinearMap.comp_assoc, add_comm]

/-- The diagonal of the forward conjugate pair is twice the real part of one
oriented detector crossing. -/
theorem inner_sourceGatePhysicalForwardSymmetricResponse_eq_two_re
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ⟪x, sourceGatePhysicalForwardSymmetricResponse owner lambda family x⟫_ℂ =
      ((2 * (⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourceActualBandForwardCoframe lambda family x)⟫_ℂ).re : ℝ) : ℂ) := by
  let crossing := ⟪sourceInclusion lambda x,
    detectorOperator owner
      (sourceActualBandForwardCoframe lambda family x)⟫_ℂ
  have hfirst :
      ⟪x, ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        sourceActualBandForwardCoframe lambda family) x⟫_ℂ = crossing := by
    dsimp only [crossing]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hsecond :
      ⟪x, ((sourceActualBandForwardCoframe lambda family)† ∘L
        detectorOperator owner ∘L sourceInclusion lambda) x⟫_ℂ =
          star crossing := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    calc
      ⟪sourceActualBandForwardCoframe lambda family x,
          detectorOperator owner (sourceInclusion lambda x)⟫_ℂ =
          ⟪sourceActualBandForwardCoframe lambda family x,
            ((detectorOperator owner)†) (sourceInclusion lambda x)⟫_ℂ := by
        rw [(detectorOperator_isSelfAdjoint owner).adjoint_eq]
      _ = ⟪detectorOperator owner
            (sourceActualBandForwardCoframe lambda family x),
          sourceInclusion lambda x⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = star crossing := by
        exact (inner_conj_symm (𝕜 := ℂ)
          (detectorOperator owner
            (sourceActualBandForwardCoframe lambda family x))
          (sourceInclusion lambda x)).symm
  rw [sourceGatePhysicalForwardSymmetricResponse]
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  rw [hfirst, hsecond]
  dsimp only [crossing]
  rw [Complex.star_def, Complex.add_conj]

/-- The diagonal of the complete physical leakage crossing has the expected
ambient detector pairing. -/
theorem inner_sourceGatePhysicalLeakageCrossingResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ⟪x, sourceGatePhysicalLeakageCrossingResponse owner lambda family x⟫_ℂ =
      ⟪sourceInclusion lambda x,
        detectorOperator owner (sourcePhysicalCoframeLeakage lambda family x)⟫_ℂ := by
  rw [sourceGatePhysicalLeakageCrossingResponse]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The exact signed diagonal of the detector-only Gate owner.  No ordinary
trace has been distributed over the two displayed terms. -/
theorem inner_sourceGatePhysicalDetectorOffDiagonalResponse_eq_two_re_add_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ⟪x, sourceGatePhysicalDetectorOffDiagonalResponse owner lambda family x⟫_ℂ =
      ((2 * (⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourceActualBandForwardCoframe lambda family x)⟫_ℂ).re : ℝ) : ℂ) +
      ⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourcePhysicalCoframeLeakage lambda family x)⟫_ℂ := by
  rw [sourceGatePhysicalDetectorOffDiagonalResponse_eq_forward_add_leakage]
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  rw [inner_sourceGatePhysicalForwardSymmetricResponse_eq_two_re,
    inner_sourceGatePhysicalLeakageCrossingResponse]

/-- The Gate-facing operator has the same signed pointwise diagonal. -/
theorem inner_lowerFactorGaugedResponse_eq_two_re_add_physicalLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ⟪x, lowerFactorGaugedActualBandCompletedRelativeResponse
      owner lambda family x⟫_ℂ =
      ((2 * (⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourceActualBandForwardCoframe lambda family x)⟫_ℂ).re : ℝ) : ℂ) +
      ⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourcePhysicalCoframeLeakage lambda family x)⟫_ℂ := by
  rw [lowerFactorGaugedResponse_eq_detectorOffDiagonal]
  exact
    inner_sourceGatePhysicalDetectorOffDiagonalResponse_eq_two_re_add_leakage
      owner lambda family x

/-- Every imaginary diagonal contribution comes from the complete physical
leakage crossing; the forward conjugate pair contributes only a real scalar. -/
theorem inner_lowerFactorGaugedResponse_im_eq_physicalLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    (⟪x, lowerFactorGaugedActualBandCompletedRelativeResponse
      owner lambda family x⟫_ℂ).im =
      (⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourcePhysicalCoframeLeakage lambda family x)⟫_ℂ).im := by
  rw [inner_lowerFactorGaugedResponse_eq_two_re_add_physicalLeakage]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add]

end CCM24FiniteSGatePhysicalSignedDiagonal
end CCM25Concrete
end Source
end ConnesWeilRH
