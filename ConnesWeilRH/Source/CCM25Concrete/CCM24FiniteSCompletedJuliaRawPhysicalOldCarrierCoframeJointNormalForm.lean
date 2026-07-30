/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeFactorization

/-!
# Complete signed coframe normal form

The coframe divide-and-conquer row must be regrouped before any norm estimate.
This file exposes the exact regrouping

```text
signedTelescope
  = ambientRow * (H† - I) + completeBoundaryResidual,
```

where `H` is the normalized one-prime Euler transport.  The residual contains
the hard boundary term, the known row, and the ambient row added back by the
regrouping.  No component of this residual is estimated or discarded here.
The point is to make the one remaining source question explicit: does this
single residual factor through the moving-boundary channel?
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointNormalForm

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "OldRow" lambda =>
  finiteSCarrier →L[ℂ] sourceSoninCarrier lambda

/-! ## Exact ambient-plus-residual regrouping -/

/-- The ambient row already present in the hard-row expansion. -/
noncomputable def coframeJointGapAmbientRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : OldRow lambda :=
  coframeHardAmbientRow owner lambda p S

/-- The complete signed remainder after the ambient difference is extracted.

The `+ ambientRow` term is intentional: it changes `ambientRow * H†` into
`ambientRow * (H† - I)`, while preserving exact equality. -/
noncomputable def coframeJointGapBoundaryResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : OldRow lambda :=
  coframeHardBoundaryRow owner lambda p S +
    coframeKnownBoundedRow owner lambda p S +
    coframeJointGapAmbientRow owner lambda p S

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_ambientDifference_add_jointBoundaryResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      coframeJointGapAmbientRow owner lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)† -
        coframeJointGapAmbientRow owner lambda p S +
        coframeJointGapBoundaryResidualRow owner lambda p S := by
  rw [coframeJointGapAmbientRow, coframeJointGapBoundaryResidualRow,
    signedTelescope_eq_hard_add_known,
    coframeHardRow_eq_ambient_add_boundary]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    coframeJointGapAmbientRow, map_add]
  abel

/-! ## The exact source-facing remaining factorization target -/

/-- The residual factorization is exactly the missing moving-boundary half of
the full signed producer.  It is stated separately so a source theorem can
prove it without splitting the signed telescope into independent rows. -/
structure SuffixRawOldCarrierCoframeJointBoundaryFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (ambientBound boundaryBound : ℝ) where
  ambient_bound_nonneg : 0 ≤ ambientBound
  boundary_bound_nonneg : 0 ≤ boundaryBound
  ambient_norm_le :
    ‖coframeJointGapAmbientRow owner lambda p S‖ ≤ ambientBound
  boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  boundary_norm_le : ‖boundaryRow‖ ≤ boundaryBound
  factorization :
    boundaryRow ∘L
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transport) =
      coframeJointGapBoundaryResidualRow owner lambda p S

/-! ## Direct range test for the complete residual -/

/-- The proposed moving-boundary factorization has this exact
scalar-normalized range condition.  It is a source proposition, not a theorem
derived from the current algebraic ledger. -/
def coframeJointGapBoundaryResidualRowScalarRangeAnnihilation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    Prop :=
  coframeJointGapBoundaryResidualRow owner lambda p S ∘L
      (scalarNormalizedPrimeEulerInverse p)† ∘L
      (suffixEulerFrameSchurStep lambda p S).newFrame = 0

/-- Exact readback of the range test.  The residual is zero on the tested
range exactly when the synchronized gap is supplied by the ambient difference
on that range; no such covariance identity is assumed here. -/
theorem coframeJointGapBoundaryResidualRow_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq_gap_readback
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeJointGapBoundaryResidualRow owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (coframeBoundaryMomentGap owner lambda p S ∘L
            (suffixEulerFrameReverseTransition lambda p S)†) -
        coframeJointGapAmbientRow owner lambda p S ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame +
        coframeJointGapAmbientRow owner lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame := by
  have hnormal :=
    suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_ambientDifference_add_jointBoundaryResidual
      owner lambda p S
  have hC :
      coframeJointGapBoundaryResidualRow owner lambda p S =
        suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S -
            coframeJointGapAmbientRow owner lambda p S ∘L
              (normalizedPrimeEulerFrameTransport p)† +
          coframeJointGapAmbientRow owner lambda p S := by
    rw [hnormal]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    abel
  have hleft :=
    scalarNormalizedPrimeEulerInverse_comp_normalizedPrimeEulerFrameTransport p
  have hadjoint :
      (normalizedPrimeEulerFrameTransport p)† ∘L
          (scalarNormalizedPrimeEulerInverse p)† =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    have h := congrArg ContinuousLinearMap.adjoint hleft
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id] using h
  have hmiddle :
      coframeJointGapAmbientRow owner lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)† ∘L
            (scalarNormalizedPrimeEulerInverse p)† ∘L
              (suffixEulerFrameSchurStep lambda p S).newFrame =
        coframeJointGapAmbientRow owner lambda p S ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame := by
    calc
      coframeJointGapAmbientRow owner lambda p S ∘L
            (normalizedPrimeEulerFrameTransport p)† ∘L
              (scalarNormalizedPrimeEulerInverse p)† ∘L
                (suffixEulerFrameSchurStep lambda p S).newFrame =
          coframeJointGapAmbientRow owner lambda p S ∘L
            ((normalizedPrimeEulerFrameTransport p)† ∘L
              (scalarNormalizedPrimeEulerInverse p)†) ∘L
                (suffixEulerFrameSchurStep lambda p S).newFrame := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = coframeJointGapAmbientRow owner lambda p S ∘L
            (ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
              (suffixEulerFrameSchurStep lambda p S).newFrame := by
        rw [hadjoint]
      _ = coframeJointGapAmbientRow owner lambda p S ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame := by
        simp
  calc
    coframeJointGapBoundaryResidualRow owner lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame =
        (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S -
            coframeJointGapAmbientRow owner lambda p S ∘L
              (normalizedPrimeEulerFrameTransport p)† +
          coframeJointGapAmbientRow owner lambda p S) ∘L
            (scalarNormalizedPrimeEulerInverse p)† ∘L
              (suffixEulerFrameSchurStep lambda p S).newFrame := by
      rw [hC]
    _ = suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame -
        coframeJointGapAmbientRow owner lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)† ∘L
            (scalarNormalizedPrimeEulerInverse p)† ∘L
              (suffixEulerFrameSchurStep lambda p S).newFrame +
        coframeJointGapAmbientRow owner lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    _ = (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (coframeBoundaryMomentGap owner lambda p S ∘L
            (suffixEulerFrameReverseTransition lambda p S)†) -
        coframeJointGapAmbientRow owner lambda p S ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame +
        coframeJointGapAmbientRow owner lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame := by
      rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq,
        hmiddle]

/-- The range-factor constructor shows exactly what the source estimate must
supply: a uniform residual norm and the scalar-normalized range condition. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointBoundaryFactorData.ofResidualRangeAnnihilation
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {ambientBound boundaryBound : ℝ}
    (hambient_bound_nonneg : 0 ≤ ambientBound)
    (hboundary_bound_nonneg : 0 ≤ boundaryBound)
    (hambient_norm_le :
      ‖coframeJointGapAmbientRow owner lambda p S‖ ≤ ambientBound)
    (hboundary_norm_le :
      ‖coframeJointGapBoundaryResidualRow owner lambda p S‖ ≤ boundaryBound)
    (hannihilate :
      coframeJointGapBoundaryResidualRowScalarRangeAnnihilation
        owner lambda p S) :
    SuffixRawOldCarrierCoframeJointBoundaryFactorData owner lambda p S
      ambientBound (boundaryBound * 8) := by
  let row := coframeJointGapBoundaryResidualRow owner lambda p S
  let inverse := scalarNormalizedPrimeEulerInverse p
  let frame := (suffixEulerFrameSchurStep lambda p S).newFrame
  have hframe :
      ContinuousLinearMap.adjoint frame ∘L frame =
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [frame] using
      (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have htransport :
      (suffixEulerFrameSchurStep lambda p S).transport ∘L inverse =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    simpa only [inverse, suffixEulerFrameSchurStep] using
      normalizedPrimeEulerFrameTransport_comp_scalarNormalizedInverse p
  have hannihilate' :
      row ∘L ContinuousLinearMap.adjoint inverse ∘L frame = 0 := by
    simpa only [row, inverse, frame,
      coframeJointGapBoundaryResidualRowScalarRangeAnnihilation] using
      hannihilate
  have hfactor :=
    rangeFactor_comp_complement_comp_transportAdjoint_eq row
      (suffixEulerFrameSchurStep lambda p S).transport inverse frame
      hframe htransport hannihilate'
  have hinverse : ‖inverse‖ ≤ (8 : ℝ) := by
    simpa only [inverse] using
      scalarNormalizedPrimeEulerInverse_norm_le_eight p
  have hnorm : ‖rangeFactor row inverse frame‖ ≤ boundaryBound * 8 := by
    exact rangeFactor_norm_le row inverse frame boundaryBound 8 hframe
      hboundary_norm_le hinverse hboundary_bound_nonneg (by norm_num)
  refine
    { ambient_bound_nonneg := hambient_bound_nonneg
      boundary_bound_nonneg := mul_nonneg hboundary_bound_nonneg (by norm_num)
      ambient_norm_le := hambient_norm_le
      boundaryRow := rangeFactor row inverse frame
      boundary_norm_le := hnorm
      factorization := ?_ }
  simpa only [row, inverse, frame] using hfactor

/-- A complete residual factor gives the existing step-level readout, with the
ambient and boundary terms combined only after the exact signed regrouping. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointBoundaryFactorData.toStepReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {ambientBound boundaryBound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointBoundaryFactorData owner lambda p S
      ambientBound boundaryBound) :
    SuffixRawOldCarrierCoframeStepReadoutData owner lambda p S
      (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S)
      ambientBound boundaryBound := by
  refine
    { ambient_bound_nonneg := data.ambient_bound_nonneg
      boundary_bound_nonneg := data.boundary_bound_nonneg
      ambientRow := coframeJointGapAmbientRow owner lambda p S
      boundaryRow := data.boundaryRow
      ambient_norm_le := data.ambient_norm_le
      boundary_norm_le := data.boundary_norm_le
      decomposition := ?_ }
  calc
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
        coframeJointGapAmbientRow owner lambda p S ∘L
            (normalizedPrimeEulerFrameTransport p)† -
          coframeJointGapAmbientRow owner lambda p S +
          coframeJointGapBoundaryResidualRow owner lambda p S :=
      suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_ambientDifference_add_jointBoundaryResidual
        owner lambda p S
    _ = coframeJointGapAmbientRow owner lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)† -
        coframeJointGapAmbientRow owner lambda p S +
        data.boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) := by
      rw [data.factorization]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH
