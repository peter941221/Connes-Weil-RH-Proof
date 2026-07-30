/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger

/-!
# Balanced physical cocycle

Proof 664 leaves the adjacent difference of a completed target-boundary/raw
ledger.  This module recombines those two terms before taking a norm.

For the literal suffix frame `K_S`, Gram inverse square root `R_S`, inverse
partner `L_S`, frame detector compression `A_S`, and fixed compression `B_0`,
set

```text
Z_S = FirstJetPhysical_S L_S
    + (A_S R_S - R_S A_S)
    + (L_S B_0 - B_0 L_S).
```

The target boundary and balanced raw response then satisfy the exact
single-suffix identity

```text
TargetBoundary_S + BalancedRaw_S = R_S Z_S.
```

After taking the adjacent difference and restoring the ambient frame, the
active Bone 1A column becomes

```text
K_(p::S) (X_S - X_(p::S)) R_S
  = U_(p::S)
      (Z_(p::S) - (1 + q_p) T_(p,S) Z_S) R_S.
```

The polar frame `U_(p::S)` is isometric, so it can be removed from the
operator norm exactly.  This is a same-object normal form, not a uniform
estimate of the remaining physical cocycle.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPhysicalCocycle

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRawIntertwiningAmbientReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

local notation "SourceToFinite" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    finiteSCarrier

private theorem balanced_left_comp_sub_eq_adjoint_right_comp_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (gram compression base : H →L[ℂ] H)
    (hgram : IsSelfAdjoint gram)
    (hcompression : IsSelfAdjoint compression)
    (hbase : IsSelfAdjoint base) :
    gram ∘L compression - base = (compression ∘L gram - base)† := by
  have hadjointSub :
      (compression ∘L gram - base)† =
        (compression ∘L gram)† - base† := by
    apply ContinuousLinearMap.ext
    intro u
    exact ext_inner_right ℂ fun v => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [hadjointSub, ContinuousLinearMap.adjoint_comp,
    hgram.adjoint_eq, hcompression.adjoint_eq, hbase.adjoint_eq]

/-! ## Physical first jet and the two Gram orientations -/

/-- The unnormalized detector compression `A_S = K_S† W K_S`. -/
noncomputable def suffixActualBandFrameDetectorCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (suffixActualBandFrame lambda S)† ∘L detectorOperator owner ∘L
    suffixActualBandFrame lambda S

/-- The literal three-branch physical first jet.  Both orientations share
the same fixed CC20 boundary commutator. -/
noncomputable def suffixActualBandPhysicalFirstJetResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      suffixActualBandForwardCoframe lambda S -
    (suffixActualBandForwardCoframe lambda S)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

/-- The named physical first jet is the independently constructed finite
Euler Sonin response. -/
theorem suffixActualBandPhysicalFirstJetResponse_eq_finiteEulerSoninResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandPhysicalFirstJetResponse owner lambda S =
      suffixActualBandFiniteEulerSoninResponse owner lambda S := by
  simpa only [suffixActualBandPhysicalFirstJetResponse] using
    (suffixActualBandFiniteEulerSoninResponse_eq_commonPhysicalFirstJet
      owner lambda S).symm

/-- The physical first jet is the root-factor first-jet cycle used by the
raw quadratic response. -/
theorem suffixActualBandPhysicalFirstJetResponse_eq_firstJetCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandPhysicalFirstJetResponse owner lambda S =
      suffixActualBandFirstJetCycledResponse owner lambda S := by
  rw [suffixActualBandPhysicalFirstJetResponse_eq_finiteEulerSoninResponse,
    suffixActualBandFiniteEulerSoninResponse_eq_firstJetCycle]

/-- The endpoint cycle is the negative right-ordered source Gram response. -/
theorem suffixActualBandEndpointCycledResponse_eq_neg_sourceGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandEndpointCycledResponse owner lambda S =
      -suffixActualBandSourceGramResponse owner lambda S := by
  rw [suffixActualBandEndpointCycledResponse_eq_neg_threeBranch,
    suffixActualBandSourceGramResponse_eq_threeBranch]

/-- The raw response is the physical first jet plus the right-ordered Gram
response `A_S G_S⁻¹ - B_0`. -/
theorem suffixActualBandRawQuadraticCycledResponse_eq_physical_add_sourceGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandRawQuadraticCycledResponse owner lambda S =
      suffixActualBandPhysicalFirstJetResponse owner lambda S +
        suffixActualBandSourceGramResponse owner lambda S := by
  rw [suffixActualBandRawQuadraticCycledResponse,
    ← suffixActualBandPhysicalFirstJetResponse_eq_firstJetCycle,
    suffixActualBandEndpointCycledResponse_eq_neg_sourceGramResponse]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  abel

/-- The literal frame detector compression is self-adjoint. -/
theorem suffixActualBandFrameDetectorCompression_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixActualBandFrameDetectorCompression owner lambda S)† =
      suffixActualBandFrameDetectorCompression owner lambda S := by
  rw [suffixActualBandFrameDetectorCompression,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (CCM24FiniteSGramResponse.detectorOperator_isSelfAdjoint owner).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The fixed source detector compression `B_0` is self-adjoint. -/
theorem suffixActualBandFixedSourceDetectorCompression_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (suffixActualBandFixedSourceDetectorCompression owner lambda)† =
      suffixActualBandFixedSourceDetectorCompression owner lambda := by
  rw [suffixActualBandFixedSourceDetectorCompression,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (CCM24FiniteSGramResponse.detectorOperator_isSelfAdjoint owner).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The target boundary is the negative adjoint of the right-ordered Gram
response.  This records the orientation used in the later cancellation. -/
theorem suffixActualBandTargetProjectionBoundaryResponse_eq_neg_adjoint_sourceGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandTargetProjectionBoundaryResponse owner lambda S =
      -(suffixActualBandSourceGramResponse owner lambda S)† := by
  rw [← suffixActualBandLeftOrderedSourceBandGramResponse_eq_targetBoundary]
  change
    suffixActualBandFixedSourceDetectorCompression owner lambda -
        suffixActualBandGramInv lambda S ∘L
          suffixActualBandFrameDetectorCompression owner lambda S =
      -(suffixActualBandFrameDetectorCompression owner lambda S ∘L
          suffixActualBandGramInv lambda S -
        suffixActualBandFixedSourceDetectorCompression owner lambda)†
  have horder := balanced_left_comp_sub_eq_adjoint_right_comp_sub
    (suffixActualBandGramInv lambda S)
    (suffixActualBandFrameDetectorCompression owner lambda S)
    (suffixActualBandFixedSourceDetectorCompression owner lambda)
    (parameterizedSoninGramInv_isSelfAdjoint
      lambda 1 S (by norm_num))
    (suffixActualBandFrameDetectorCompression_adjoint_eq owner lambda S)
    (suffixActualBandFixedSourceDetectorCompression_adjoint_eq owner lambda)
  calc
    suffixActualBandFixedSourceDetectorCompression owner lambda -
        suffixActualBandGramInv lambda S ∘L
          suffixActualBandFrameDetectorCompression owner lambda S =
      -(suffixActualBandGramInv lambda S ∘L
          suffixActualBandFrameDetectorCompression owner lambda S -
        suffixActualBandFixedSourceDetectorCompression owner lambda) := by
          abel
    _ = -(suffixActualBandFrameDetectorCompression owner lambda S ∘L
          suffixActualBandGramInv lambda S -
        suffixActualBandFixedSourceDetectorCompression owner lambda)† :=
      congrArg Neg.neg horder

/-! ## Single-suffix balanced physical factorization -/

/-- The inverse Gram followed by the frame gauge collapses to the inverse
Gram square root. -/
theorem suffixActualBandGramInv_comp_metricFrameGauge_eq_coframeSqrt
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandGramInv lambda S ∘L
        suffixActualBandMetricFrameGauge lambda S =
      suffixActualBandMetricCoframeSqrt lambda S := by
  have hsquare :
      suffixActualBandMetricCoframeSqrt lambda S ∘L
          suffixActualBandMetricCoframeSqrt lambda S =
        suffixActualBandGramInv lambda S := by
    simpa only [suffixActualBandMetricCoframeSqrt,
      suffixActualBandGramInv] using
        parameterizedSoninGramInvSqrt_mul_self
          lambda 1 S (by norm_num)
  rw [← hsquare, ContinuousLinearMap.comp_assoc,
    suffixActualBandMetricCoframeSqrt_comp_frameGauge,
    ContinuousLinearMap.comp_id]

/-- The two Proof 664 terms completed at one suffix. -/
noncomputable def suffixActualBandBalancedTargetRawResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandTargetProjectionBoundaryResponse owner lambda S +
    suffixActualBandBalancedRawQuadraticResponse owner lambda S

/-- The two explicit metric-gauge commutators. -/
noncomputable def suffixActualBandBalancedGaugeCommutatorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (suffixActualBandFrameDetectorCompression owner lambda S ∘L
      suffixActualBandMetricCoframeSqrt lambda S -
    suffixActualBandMetricCoframeSqrt lambda S ∘L
      suffixActualBandFrameDetectorCompression owner lambda S) +
  (suffixActualBandMetricFrameGauge lambda S ∘L
      suffixActualBandFixedSourceDetectorCompression owner lambda -
    suffixActualBandFixedSourceDetectorCompression owner lambda ∘L
      suffixActualBandMetricFrameGauge lambda S)

/-- The physical cocycle kernel `Z_S`: one physical first jet and the two
metric-gauge commutators, kept in their signed combination. -/
noncomputable def suffixActualBandBalancedPhysicalCocycleKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandPhysicalFirstJetResponse owner lambda S ∘L
      suffixActualBandMetricFrameGauge lambda S +
    suffixActualBandBalancedGaugeCommutatorResponse owner lambda S

/-- Exact same-suffix cancellation of the target boundary against the metric
part of the balanced raw response. -/
theorem suffixActualBandBalancedTargetRawResponse_eq_coframe_physicalCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedTargetRawResponse owner lambda S =
      suffixActualBandMetricCoframeSqrt lambda S ∘L
        suffixActualBandBalancedPhysicalCocycleKernel owner lambda S := by
  rw [suffixActualBandBalancedTargetRawResponse,
    ← suffixActualBandLeftOrderedSourceBandGramResponse_eq_targetBoundary,
    suffixActualBandBalancedRawQuadraticResponse,
    suffixActualBandRawQuadraticCycledResponse_eq_physical_add_sourceGram]
  have hsquare :
      suffixActualBandMetricCoframeSqrt lambda S ∘L
          suffixActualBandMetricCoframeSqrt lambda S =
        suffixActualBandGramInv lambda S := by
    simpa only [suffixActualBandMetricCoframeSqrt,
      suffixActualBandGramInv] using
        parameterizedSoninGramInvSqrt_mul_self
          lambda 1 S (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  have hsquareAt := congrArg
    (fun operator : SourceOp lambda =>
      operator (suffixActualBandFrameDetectorCompression owner lambda S x))
    hsquare
  have hcoframeAt := congrArg
    (fun operator : SourceOp lambda =>
      operator
        (suffixActualBandFixedSourceDetectorCompression owner lambda x))
    (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
  have hgramAt := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixActualBandGramInv_comp_metricFrameGauge_eq_coframeSqrt lambda S)
  simp only [suffixActualBandLeftOrderedSourceBandGramResponse,
    suffixActualBandSourceGramResponse,
    suffixActualBandFrameDetectorCompression,
    suffixActualBandFixedSourceDetectorCompression,
    suffixActualBandBalancedPhysicalCocycleKernel,
    suffixActualBandBalancedGaugeCommutatorResponse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_add, map_sub] at hsquareAt hcoframeAt hgramAt ⊢
  rw [hgramAt, hsquareAt, hcoframeAt]
  abel

/-! ## Adjacent cocycle and ambient isometric readback -/

/-- The completed target/raw ledger is the adjacent difference of the two
coframe-weighted physical cocycles. -/
theorem suffixActualBandTargetRawLedger_eq_physicalCocycleDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandTargetProjectionBoundaryResponse
          owner lambda (p :: S) -
        suffixActualBandTargetProjectionBoundaryResponse owner lambda S +
        suffixActualBandBalancedRawQuadraticResponse
          owner lambda (p :: S) -
        suffixActualBandBalancedRawQuadraticResponse owner lambda S =
      suffixActualBandMetricCoframeSqrt lambda (p :: S) ∘L
          suffixActualBandBalancedPhysicalCocycleKernel
            owner lambda (p :: S) -
        suffixActualBandMetricCoframeSqrt lambda S ∘L
          suffixActualBandBalancedPhysicalCocycleKernel owner lambda S := by
  rw [← suffixActualBandBalancedTargetRawResponse_eq_coframe_physicalCocycle
      owner lambda (p :: S),
    ← suffixActualBandBalancedTargetRawResponse_eq_coframe_physicalCocycle
      owner lambda S]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandBalancedTargetRawResponse,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

/-- Proof 663's balanced mismatch difference is the same adjacent physical
cocycle difference. -/
theorem
    suffixActualBandBalancedPolarRawMismatchKernel_sub_eq_physicalCocycleDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPolarRawMismatchKernel owner lambda S -
        suffixActualBandBalancedPolarRawMismatchKernel
          owner lambda (p :: S) =
      suffixActualBandMetricCoframeSqrt lambda (p :: S) ∘L
          suffixActualBandBalancedPhysicalCocycleKernel
            owner lambda (p :: S) -
        suffixActualBandMetricCoframeSqrt lambda S ∘L
          suffixActualBandBalancedPhysicalCocycleKernel owner lambda S := by
  rw [suffixActualBandBalancedPolarRawMismatchKernel_sub_eq_targetRawLedger,
    suffixActualBandTargetRawLedger_eq_physicalCocycleDifference]

/-- The old right gauge on the longer frame is the upper Euler scalar times
the polar frame followed by the actual compressed transition. -/
theorem suffixActualBandFrame_cons_comp_oldCoframeSqrt_eq_transition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandFrame lambda (p :: S) ∘L
        suffixActualBandMetricCoframeSqrt lambda S =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        (newSuffixFrame lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S) := by
  have hscalar :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (add_pos_of_pos_of_nonneg zero_lt_one
        (ccm24PrimeEulerCoefficient_nonneg p))
  apply ContinuousLinearMap.ext
  intro x
  have hframe := congrArg
    (fun operator : SourceToFinite lambda =>
      operator (suffixActualBandMetricCoframeSqrt lambda S x))
    (newSuffixFrame_comp_metricFrameGauge_eq_parameterizedSoninFrame
      lambda (p :: S))
  rw [suffixEulerFrameTransition_eq_polarGauge]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_inv_cancel₀ hscalar, one_smul]
  simpa only [suffixActualBandFrame] using hframe.symm

/-- The source-side adjacent physical cocycle before the terminal right
coframe is attached. -/
noncomputable def suffixActualBandAdjacentPhysicalCocycleKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandBalancedPhysicalCocycleKernel owner lambda (p :: S) -
    (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
      (suffixEulerFrameTransition lambda p S ∘L
        suffixActualBandBalancedPhysicalCocycleKernel owner lambda S)

/-- The complete source cocycle column, including the terminal old coframe. -/
noncomputable def suffixActualBandBalancedPhysicalCocycleColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandAdjacentPhysicalCocycleKernel owner lambda p S ∘L
    suffixActualBandMetricCoframeSqrt lambda S

/-- Exact ambient normal form: the entire Proof 664 ledger is the isometric
polar frame applied to one source physical cocycle column. -/
theorem suffixActualBandAmbientBalancedTargetRawLedgerColumn_eq_physicalCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientBalancedTargetRawLedgerColumn
        owner lambda p S =
      newSuffixFrame lambda (p :: S) ∘L
        suffixActualBandBalancedPhysicalCocycleColumn owner lambda p S := by
  rw [suffixActualBandAmbientBalancedTargetRawLedgerColumn,
    suffixActualBandTargetRawLedger_eq_physicalCocycleDifference]
  apply ContinuousLinearMap.ext
  intro x
  have hcurrent := congrArg
    (fun operator : SourceToFinite lambda =>
      operator
        (suffixActualBandBalancedPhysicalCocycleKernel
          owner lambda (p :: S)
          (suffixActualBandMetricCoframeSqrt lambda S x)))
    (suffixActualBandFrame_comp_metricCoframeSqrt_eq_newSuffixFrame
      lambda (p :: S))
  have hprevious := congrArg
    (fun operator : SourceToFinite lambda =>
      operator
        (suffixActualBandBalancedPhysicalCocycleKernel owner lambda S
          (suffixActualBandMetricCoframeSqrt lambda S x)))
    (suffixActualBandFrame_cons_comp_oldCoframeSqrt_eq_transition
      lambda p S)
  simp only [suffixActualBandFrame,
    suffixActualBandBalancedPhysicalCocycleColumn,
    suffixActualBandAdjacentPhysicalCocycleKernel,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_smul] at hcurrent hprevious ⊢
  rw [hcurrent, hprevious]

/-! ## Route-scaled norm equivalence -/

/-- The genuine square-root-scaled source physical cocycle column. -/
noncomputable def routeScaledBalancedPhysicalCocycleColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) : SourceOp unitSoninScale :=
  ((Real.sqrt (ccm24PrimeEulerCoefficient index.prime) : ℂ)⁻¹) •
    suffixActualBandBalancedPhysicalCocycleColumn
      owner unitSoninScale index.prime index.suffix

/-- The route-scaled target/raw ledger is the polar-frame lift of the
route-scaled source physical cocycle. -/
theorem routeScaledBalancedTargetRawLedgerColumn_eq_frame_physicalCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledBalancedTargetRawLedgerColumn owner index =
      newSuffixFrame unitSoninScale (index.prime :: index.suffix) ∘L
        routeScaledBalancedPhysicalCocycleColumn owner index := by
  rw [routeScaledBalancedTargetRawLedgerColumn,
    suffixActualBandAmbientBalancedTargetRawLedgerColumn_eq_physicalCocycle,
    routeScaledBalancedPhysicalCocycleColumn]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

/-- The ambient and source route-scaled columns have exactly the same
operator norm. -/
theorem norm_routeScaledBalancedTargetRawLedgerColumn_eq_physicalCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    ‖routeScaledBalancedTargetRawLedgerColumn owner index‖ =
      ‖routeScaledBalancedPhysicalCocycleColumn owner index‖ := by
  rw [routeScaledBalancedTargetRawLedgerColumn_eq_frame_physicalCocycle]
  apply norm_isometric_postcomp_eq
  exact
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (newSuffixFrame unitSoninScale
        (index.prime :: index.suffix))).mpr (by
          simpa only [ContinuousLinearMap.one_def] using
            parameterizedSoninPolarFrame_adjoint_comp_self
              unitSoninScale 1 (index.prime :: index.suffix) (by norm_num))

/-- One bound for all route-valid source physical cocycle columns. -/
def SuffixBalancedPhysicalCocycleRouteUniformScaledBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledBalancedPhysicalCocycleColumn owner index‖ ≤ bound

/-- Proof 664's completed ledger bound and the source physical cocycle bound
are the same statement with the same constant. -/
theorem targetRawLedgerRouteUniformScaledBound_iff_physicalCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) :
    SuffixBalancedTargetRawLedgerRouteUniformScaledBound owner bound ↔
      SuffixBalancedPhysicalCocycleRouteUniformScaledBound owner bound := by
  constructor
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [← norm_routeScaledBalancedTargetRawLedgerColumn_eq_physicalCocycle]
    exact data.2 index
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [norm_routeScaledBalancedTargetRawLedgerColumn_eq_physicalCocycle]
    exact data.2 index

/-- Bone 1A is exactly the existence of a route-uniform bound for the single
square-root-scaled source physical cocycle column. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_physicalCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixBalancedPhysicalCocycleRouteUniformScaledBound owner bound := by
  rw [exists_routeUniformScaledCompleteTargetBound_iff_targetRawLedger]
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (targetRawLedgerRouteUniformScaledBound_iff_physicalCocycle
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (targetRawLedgerRouteUniformScaledBound_iff_physicalCocycle
        owner bound).mpr data⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPhysicalCocycle
end CCM25Concrete
end Source
end ConnesWeilRH
