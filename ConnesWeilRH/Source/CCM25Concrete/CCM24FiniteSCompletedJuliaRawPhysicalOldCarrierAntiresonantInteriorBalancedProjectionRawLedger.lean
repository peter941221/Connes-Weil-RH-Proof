/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualMovingProjection
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingCrossingPullback
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramOrderingBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm

/-!
# Balanced projection/raw ledger

Proof 663 reduces the remaining Bone 1A response to the adjacent difference
of one balanced source kernel `X_S`.  This module expands that kernel without
discarding either of its two moving pieces.

For the literal suffix frame `K_S`, Gram `G_S`, inverse square root `R_S`,
and inverse partner `L_S = R_S G_S`, define

```text
LeftBand_S = B_0 - G_S^-1 K_S^dagger W K_S,
BalancedRaw_S = R_S Raw_S L_S.
```

Then the exact one-suffix and adjacent ledgers are

```text
X_S = B_0 - LeftBand_S - BalancedRaw_S,

X_S - X_(p::S)
  = LeftBand_(p::S) - LeftBand_S
    + BalancedRaw_(p::S) - BalancedRaw_S.
```

The left-ordered band term is also identified with the genuine target
projection-commutator boundary response on the literal list.  The balanced
raw term remains in the same adjacent bracket.  Thus the `O(q_p)` projection
gap cannot be substituted for the complete response before a source theorem
controls their recombination.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualMovingProjection
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaRouteKernelNormalForm
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm
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
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSMovingCrossingPullback
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSRootCompletedFirstJet
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

/-! ## Literal left order and balanced raw term -/

/-- The fixed source detector compression `B_0`. -/
noncomputable def suffixActualBandFixedSourceDetectorCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : SourceOp lambda :=
  (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
    detectorOperator owner ∘L CCM24FiniteSGramResponse.sourceInclusion lambda

/-- The route-band orientation of the literal left-normalized Gram response.
It is `B_0 - G_S^-1 K_S^dagger W K_S`. -/
noncomputable def suffixActualBandLeftOrderedSourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandFixedSourceDetectorCompression owner lambda -
    suffixActualBandGramInv lambda S ∘L
      ((suffixActualBandFrame lambda S)† ∘L detectorOperator owner ∘L
        suffixActualBandFrame lambda S)

/-- The raw quadratic response in Proof 663's balanced polar gauge. -/
noncomputable def suffixActualBandBalancedRawQuadraticResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandMetricCoframeSqrt lambda S ∘L
    suffixActualBandRawQuadraticCycledResponse owner lambda S ∘L
      suffixActualBandMetricFrameGauge lambda S

/-- The root-factor definition of the fixed base response is the literal
source detector compression. -/
theorem suffixActualBandBaseDetectorResponse_eq_fixedSourceCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    suffixActualBandBaseDetectorResponse owner lambda =
      suffixActualBandFixedSourceDetectorCompression owner lambda := by
  unfold suffixActualBandBaseDetectorResponse
    suffixActualBandFixedSourceDetectorCompression actualBandBaseRootLeg
  rw [detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply]

/-- Balancing the polar detector compression removes both square-root gauges
and leaves the left-normalized unpolarized detector compression. -/
theorem suffixActualBandBalancedPolarCompression_eq_leftNormalized
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframeSqrt lambda S ∘L
        suffixPolarDetectorCompression owner lambda S ∘L
          suffixActualBandMetricFrameGauge lambda S =
      suffixActualBandGramInv lambda S ∘L
        ((suffixActualBandFrame lambda S)† ∘L detectorOperator owner ∘L
          suffixActualBandFrame lambda S) := by
  apply ContinuousLinearMap.ext
  intro x
  have hsquare := parameterizedSoninGramInvSqrt_mul_self
    lambda 1 S (by norm_num)
  have hsquareAtGram := congrArg
    (fun operator : SourceOp lambda =>
      operator (parameterizedSoninGram lambda 1 S x)) hsquare
  have hsquareAtCompression := congrArg
    (fun operator : SourceOp lambda =>
      operator (((parameterizedSoninFrame lambda 1 S)†)
        (detectorOperator owner (parameterizedSoninFrame lambda 1 S x))))
    hsquare
  have hinverse := congrArg
    (fun operator : SourceOp lambda => operator x)
    (parameterizedSoninGramInv_mul_gram lambda 1 S (by norm_num))
  have hself := parameterizedSoninGramInvSqrt_isSelfAdjoint
    lambda 1 S (by norm_num)
  simp only [ContinuousLinearMap.comp_apply] at hsquareAtGram hsquareAtCompression
  simp only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply] at hinverse
  simp only [suffixActualBandMetricCoframeSqrt,
    suffixActualBandMetricFrameGauge,
    suffixPolarDetectorCompression, newSuffixFrame,
    parameterizedSoninPolarFrame, suffixActualBandFrame,
    suffixActualBandGramInv, ContinuousLinearMap.adjoint_comp,
    hself.adjoint_eq, ContinuousLinearMap.comp_apply]
  rw [hsquareAtGram, hinverse, hsquareAtCompression]

/-- Exact single-suffix ledger for Proof 663's balanced mismatch. -/
theorem suffixActualBandBalancedPolarRawMismatchKernel_eq_projectionRawLedger
  (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPolarRawMismatchKernel owner lambda S =
      suffixActualBandFixedSourceDetectorCompression owner lambda -
        suffixActualBandLeftOrderedSourceBandGramResponse owner lambda S -
        suffixActualBandBalancedRawQuadraticResponse owner lambda S := by
  rw [suffixActualBandBalancedPolarRawMismatchKernel,
    suffixActualBandRoutePolarRawMismatchKernel]
  apply ContinuousLinearMap.ext
  intro x
  have hpolar := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixActualBandBalancedPolarCompression_eq_leftNormalized
      owner lambda S)
  simp only [suffixActualBandLeftOrderedSourceBandGramResponse,
    suffixActualBandBalancedRawQuadraticResponse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub] at hpolar ⊢
  rw [hpolar]
  abel

/-- The fixed source compression cancels only after the two suffix ledgers
are subtracted.  The projection and raw increments remain recombined. -/
theorem suffixActualBandBalancedPolarRawMismatchKernel_sub_eq_projectionRawLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPolarRawMismatchKernel owner lambda S -
        suffixActualBandBalancedPolarRawMismatchKernel
          owner lambda (p :: S) =
      suffixActualBandLeftOrderedSourceBandGramResponse
          owner lambda (p :: S) -
        suffixActualBandLeftOrderedSourceBandGramResponse owner lambda S +
        suffixActualBandBalancedRawQuadraticResponse
          owner lambda (p :: S) -
        suffixActualBandBalancedRawQuadraticResponse owner lambda S := by
  rw [suffixActualBandBalancedPolarRawMismatchKernel_eq_projectionRawLedger,
    suffixActualBandBalancedPolarRawMismatchKernel_eq_projectionRawLedger]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

/-! ## Genuine target projection-commutator readback -/

/-- The polar-frame range projection is the canonical Gram-corrected
projection of the corresponding unpolarized literal frame. -/
theorem newSuffixRangeProjection_eq_parameterizedCanonicalGramProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S =
      parameterizedCanonicalGramProjection lambda 1 S := by
  rw [newSuffixRangeProjection, newSuffixFrame,
    parameterizedCanonicalGramProjection, gramCorrectedProjection,
    ringInverse_parameterizedSoninGram lambda 1 S (by norm_num)]
  have hself := parameterizedSoninGramInvSqrt_isSelfAdjoint
    lambda 1 S (by norm_num)
  rw [parameterizedSoninPolarFrame,
    ContinuousLinearMap.adjoint_comp, hself.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  have hsquare := congrArg
    (fun operator : SourceOp lambda =>
      operator (((parameterizedSoninFrame lambda 1 S)†) x))
    (parameterizedSoninGramInvSqrt_mul_self
      lambda 1 S (by norm_num))
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (parameterizedSoninFrame lambda 1 S) hsquare

/-- The literal target detector commutator in the orientation used by the
rectangular target-collapse identity. -/
noncomputable def suffixActualBandTargetDetectorCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L newSuffixRangeProjection lambda S -
    newSuffixRangeProjection lambda S ∘L detectorOperator owner

/-- The target-collapse orientation is the negative of the repository's
standard projection-first commutator. -/
theorem suffixActualBandTargetDetectorCommutator_eq_neg_cc20Commutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandTargetDetectorCommutator owner lambda S =
      -cc20Commutator (newSuffixRangeProjection lambda S)
        (detectorOperator owner) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandTargetDetectorCommutator, cc20Commutator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply]
  abel

/-- The inner target commutator has the suffix-independent adjacent
`O(q_p)` bound.  This theorem does not bound the completed boundary response,
which still contains the surrounding inverse/forward transports. -/
theorem norm_adjacentSuffixTargetDetectorCommutatorDifference_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandTargetDetectorCommutator owner lambda (p :: S) -
        suffixActualBandTargetDetectorCommutator owner lambda S‖ ≤
      8 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
  rw [suffixActualBandTargetDetectorCommutator_eq_neg_cc20Commutator,
    suffixActualBandTargetDetectorCommutator_eq_neg_cc20Commutator]
  have hProjection : newSuffixRangeProjection lambda (p :: S) =
      oldSuffixRangeProjection lambda p S := by
    rfl
  rw [hProjection]
  have h := norm_adjacentSuffixProjectionCommutatorDifference_le
    lambda p S (detectorOperator owner)
  rw [show
      -cc20Commutator (oldSuffixRangeProjection lambda p S)
            (detectorOperator owner) -
          -cc20Commutator (newSuffixRangeProjection lambda S)
            (detectorOperator owner) =
        -(cc20Commutator (oldSuffixRangeProjection lambda p S)
            (detectorOperator owner) -
          cc20Commutator (newSuffixRangeProjection lambda S)
            (detectorOperator owner)) by abel,
    norm_neg]
  exact h

/-- Completed physical boundary response of the literal target projection
commutator.  The inverse transport, complement, commutator, and forward
transport are one exact operator product. -/
noncomputable def suffixActualBandTargetProjectionBoundaryResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
    parameterizedFiniteEulerInverse 1 S ∘L
    (ContinuousLinearMap.id ℂ finiteSCarrier -
      newSuffixRangeProjection lambda S) ∘L
    suffixActualBandTargetDetectorCommutator owner lambda S ∘L
    parameterizedFiniteEulerFactor 1 S ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

/-- The literal list projection is the transported-frame Gram projection in
the exact rectangular order needed by the target collapse. -/
theorem newSuffixRangeProjection_eq_transport_frame_gramProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S =
      parameterizedFiniteEulerFactor 1 S ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda ∘L
        suffixActualBandGramInv lambda S ∘L
        (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
        (parameterizedFiniteEulerFactor 1 S)† := by
  rw [newSuffixRangeProjection_eq_parameterizedCanonicalGramProjection,
    parameterizedCanonicalGramProjection, gramCorrectedProjection,
    ringInverse_parameterizedSoninGram lambda 1 S (by norm_num),
    parameterizedSoninFrame, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The actual target projection fixes the literal transported source frame. -/
theorem newSuffixRangeProjection_comp_parameterizedFrame_eq_frame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S ∘L
        parameterizedFiniteEulerFactor 1 S ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda =
      parameterizedFiniteEulerFactor 1 S ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda := by
  rw [newSuffixRangeProjection_eq_parameterizedCanonicalGramProjection]
  simpa only [parameterizedSoninFrame] using
    parameterizedCanonicalGramProjection_comp_frame_eq_frame
      lambda 1 S (by norm_num)

/-- The literal left-ordered band response is exactly the completed target
projection-commutator boundary response. -/
theorem suffixActualBandLeftOrderedSourceBandGramResponse_eq_targetBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandLeftOrderedSourceBandGramResponse owner lambda S =
      suffixActualBandTargetProjectionBoundaryResponse owner lambda S := by
  have hProjectionSq :
      newSuffixRangeProjection lambda S ∘L
          newSuffixRangeProjection lambda S =
        newSuffixRangeProjection lambda S := by
    rw [newSuffixRangeProjection_eq_parameterizedCanonicalGramProjection]
    simpa only [ContinuousLinearMap.mul_def] using
      (parameterizedCanonicalGramProjection_isStarProjection
        lambda 1 S (by norm_num)).isIdempotentElem
  have hCollapse := rectangular_isometric_targetCommutator_collapse
    (CCM24FiniteSGramResponse.sourceInclusion lambda)
    (parameterizedFiniteEulerFactor 1 S)
    (parameterizedFiniteEulerInverse 1 S)
    (detectorOperator owner)
    (newSuffixRangeProjection lambda S)
    (suffixActualBandGramInv lambda S)
    (CCM24FiniteSGramResponse.sourceInclusion_adjoint_comp_self lambda)
    (by
      simpa only [ContinuousLinearMap.mul_def,
        ContinuousLinearMap.one_def] using
        parameterizedFiniteEulerInverse_mul_factor 1 S (by norm_num))
    (newSuffixRangeProjection_eq_transport_frame_gramProjection lambda S)
    hProjectionSq
    (newSuffixRangeProjection_comp_parameterizedFrame_eq_frame lambda S)
    (by
      rw [parameterizedFiniteEulerFactor_one]
      exact
        (CCM24FiniteSGramResponse.detectorOperator_comp_finiteEulerTransport
          owner S).symm)
  have hCollapse' :
      suffixActualBandGramInv lambda S ∘L
            ((parameterizedFiniteEulerFactor 1 S ∘L
              CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
              detectorOperator owner ∘L
              (parameterizedFiniteEulerFactor 1 S ∘L
                CCM24FiniteSGramResponse.sourceInclusion lambda)) -
          (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
            detectorOperator owner ∘L
              CCM24FiniteSGramResponse.sourceInclusion lambda =
        -suffixActualBandTargetProjectionBoundaryResponse owner lambda S := by
    simpa only [suffixActualBandTargetProjectionBoundaryResponse,
      suffixActualBandTargetDetectorCommutator] using hCollapse
  have hCollapse'' :
      suffixActualBandGramInv lambda S ∘L
            ((suffixActualBandFrame lambda S)† ∘L
              detectorOperator owner ∘L suffixActualBandFrame lambda S) -
          suffixActualBandFixedSourceDetectorCompression owner lambda =
        -suffixActualBandTargetProjectionBoundaryResponse owner lambda S := by
    simpa only [suffixActualBandFrame, parameterizedSoninFrame,
      suffixActualBandFixedSourceDetectorCompression] using hCollapse'
  rw [suffixActualBandLeftOrderedSourceBandGramResponse]
  calc
    suffixActualBandFixedSourceDetectorCompression owner lambda -
        suffixActualBandGramInv lambda S ∘L
          ((suffixActualBandFrame lambda S)† ∘L
            detectorOperator owner ∘L suffixActualBandFrame lambda S) =
      -(suffixActualBandGramInv lambda S ∘L
          ((suffixActualBandFrame lambda S)† ∘L
            detectorOperator owner ∘L suffixActualBandFrame lambda S) -
        suffixActualBandFixedSourceDetectorCompression owner lambda) := by
          abel
    _ = -(-suffixActualBandTargetProjectionBoundaryResponse
        owner lambda S) := congrArg Neg.neg hCollapse''
    _ = suffixActualBandTargetProjectionBoundaryResponse
        owner lambda S := neg_neg _

/-- Final exact Proof 664 ledger: the projection-commutator increment and the
balanced raw increment are the two parts of one adjacent response. -/
theorem suffixActualBandBalancedPolarRawMismatchKernel_sub_eq_targetRawLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPolarRawMismatchKernel owner lambda S -
        suffixActualBandBalancedPolarRawMismatchKernel
          owner lambda (p :: S) =
      suffixActualBandTargetProjectionBoundaryResponse
          owner lambda (p :: S) -
        suffixActualBandTargetProjectionBoundaryResponse owner lambda S +
        suffixActualBandBalancedRawQuadraticResponse
          owner lambda (p :: S) -
        suffixActualBandBalancedRawQuadraticResponse owner lambda S := by
  rw [suffixActualBandBalancedPolarRawMismatchKernel_sub_eq_projectionRawLedger,
    suffixActualBandLeftOrderedSourceBandGramResponse_eq_targetBoundary,
    suffixActualBandLeftOrderedSourceBandGramResponse_eq_targetBoundary]

/-! ## Active route readback -/

/-- The completed ambient column containing the target-boundary and balanced
raw increments before the square-root route scaling. -/
noncomputable def suffixActualBandAmbientBalancedTargetRawLedgerColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  parameterizedSoninFrame lambda 1 (p :: S) ∘L
    (suffixActualBandTargetProjectionBoundaryResponse
          owner lambda (p :: S) -
        suffixActualBandTargetProjectionBoundaryResponse owner lambda S +
        suffixActualBandBalancedRawQuadraticResponse
          owner lambda (p :: S) -
        suffixActualBandBalancedRawQuadraticResponse owner lambda S) ∘L
    suffixActualBandMetricCoframeSqrt lambda S

/-- Proof 663's ambient balanced difference is exactly the completed
target-boundary/raw ledger column. -/
theorem
    suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn_eq_targetRawLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn
        owner lambda p S =
      suffixActualBandAmbientBalancedTargetRawLedgerColumn
        owner lambda p S := by
  rw [suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn,
    suffixActualBandAmbientBalancedTargetRawLedgerColumn,
    suffixActualBandBalancedPolarRawMismatchKernel_sub_eq_targetRawLedger]

/-- The completed target/raw column with the genuine `q_p^(-1/2)` route
scaling from Proof 663. -/
noncomputable def routeScaledBalancedTargetRawLedgerColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    SourceToFinite unitSoninScale :=
  ((Real.sqrt (ccm24PrimeEulerCoefficient index.prime) : ℂ)⁻¹) •
    suffixActualBandAmbientBalancedTargetRawLedgerColumn
      owner unitSoninScale index.prime index.suffix

/-- The route-scaled Proof 663 column and the completed target/raw ledger
column are literally the same operator. -/
theorem routeScaledBalancedPolarGaugeDifferenceColumn_eq_targetRawLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledBalancedPolarGaugeDifferenceColumn owner index =
      routeScaledBalancedTargetRawLedgerColumn owner index := by
  rw [routeScaledBalancedPolarGaugeDifferenceColumn,
    routeScaledBalancedTargetRawLedgerColumn,
    suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn_eq_targetRawLedger]

/-- One bound for all route-valid completed target/raw ledger columns. -/
def SuffixBalancedTargetRawLedgerRouteUniformScaledBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledBalancedTargetRawLedgerColumn owner index‖ ≤ bound

/-- Proof 663's balanced-gauge bound and the completed target/raw ledger
bound are the same statement with the same constant. -/
theorem
    balancedPolarGaugeRouteUniformScaledDifferenceBound_iff_targetRawLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) :
    SuffixBalancedPolarGaugeRouteUniformScaledDifferenceBound owner bound ↔
      SuffixBalancedTargetRawLedgerRouteUniformScaledBound owner bound := by
  constructor
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [← routeScaledBalancedPolarGaugeDifferenceColumn_eq_targetRawLedger]
    exact data.2 index
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [routeScaledBalancedPolarGaugeDifferenceColumn_eq_targetRawLedger]
    exact data.2 index

/-- Bone 1A is exactly the existence of a route-uniform bound for the
completed square-root-scaled target-boundary/raw ledger column. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_targetRawLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixBalancedTargetRawLedgerRouteUniformScaledBound owner bound := by
  rw [exists_routeUniformScaledCompleteTargetBound_iff_polarGaugeDifference]
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (balancedPolarGaugeRouteUniformScaledDifferenceBound_iff_targetRawLedger
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (balancedPolarGaugeRouteUniformScaledDifferenceBound_iff_targetRawLedger
        owner bound).mpr data⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
end CCM25Concrete
end Source
end ConnesWeilRH
