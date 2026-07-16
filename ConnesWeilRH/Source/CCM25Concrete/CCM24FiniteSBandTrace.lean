/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-!
# Root-sandwiched finite-S Sonin-band trace

The raw convolution operator is not Hilbert--Schmidt on the whole line, so it
may not be cycled through the finite-S projection difference.  This module
uses the exact dual-frame factorization only as an algebraic cancellation
ledger.  The raw frame legs are deliberately not promoted to trace-legality
premises; the final owner is the completed source commutator.

The resulting source-cycle operator is exactly the negative of the Sonin
projection Gram response, hence has the route sign for `B_S-B_0`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSBandTrace

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open scoped InnerProduct

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The selected convolution root `C`. -/
noncomputable def rootConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  cc20GlobalLogConvolution owner.sourceTest.involution.test

/-- The trace-compatible route response `C(B_S-B_0)C†`. -/
noncomputable def rootSandwichedBandResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L soninBandDifference lambda family ∘L
    (rootConvolution owner)†

/-- The transported-frame completed crossing `C A`. -/
noncomputable def transportedFrameLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L finiteEulerFrame lambda family

/-- The target dual-frame displacement `C(J-F)`. -/
noncomputable def targetCrossingLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L
    (sourceInclusion lambda - finiteEulerDualFrame lambda family)

/-- The fixed source leg `C J`. -/
noncomputable def sourceFrameLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L sourceInclusion lambda

/-- The source/frame displacement `C(J-A)`. -/
noncomputable def sourceCrossingLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L
    (sourceInclusion lambda - finiteEulerFrame lambda family)

theorem transportedFrameLeg_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (transportedFrameLeg owner lambda family)† =
      (finiteEulerFrame lambda family)† ∘L (rootConvolution owner)† := by
  rw [transportedFrameLeg, ContinuousLinearMap.adjoint_comp]

theorem sourceCrossingLeg_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceCrossingLeg owner lambda family)† =
      ((sourceInclusion lambda)† - (finiteEulerFrame lambda family)†) ∘L
        (rootConvolution owner)† := by
  rw [sourceCrossingLeg, ContinuousLinearMap.adjoint_comp]
  congr 1
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]

/-- The two completed ambient crossings.  They are kept as one signed
operator before any estimate. -/
noncomputable def completedBandCrossings
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  targetCrossingLeg owner lambda family ∘L
      (transportedFrameLeg owner lambda family)† +
    sourceFrameLeg owner lambda ∘L
      (sourceCrossingLeg owner lambda family)†

/-- The root-sandwiched band response is literally the completed two-crossing
operator, not merely trace-equivalent to it. -/
theorem rootSandwichedBandResponse_eq_completedCrossings
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rootSandwichedBandResponse owner lambda family =
      completedBandCrossings owner lambda family := by
  rw [rootSandwichedBandResponse, completedBandCrossings,
    soninBandDifference_eq_neg_soninProjectionDifference,
    bandDifference_eq_dualFrame_twoCrossing,
    transportedFrameLeg_adjoint, sourceCrossingLeg_adjoint]
  simp only [rootConvolution, targetCrossingLeg, sourceFrameLeg]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_add,
    map_sub, map_neg]
  abel

/-- The source-carrier cycle of the same two completed crossings. -/
noncomputable def sourceCycledBandResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (transportedFrameLeg owner lambda family)† ∘L
      targetCrossingLeg owner lambda family +
    (sourceCrossingLeg owner lambda family)† ∘L
      sourceFrameLeg owner lambda

/-- The cycled route-band response is the negative Sonin-projection Gram
response.  This is the exact `B=E-R` sign. -/
theorem sourceCycledBandResponse_eq_neg_sourceGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceCycledBandResponse owner lambda family =
      -sourceGramResponse owner lambda family := by
  rw [sourceCycledBandResponse, sourceGramResponse]
  rw [transportedFrameLeg_adjoint, sourceCrossingLeg_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [targetCrossingLeg, sourceFrameLeg, rootConvolution,
    detectorOperator, finiteEulerDualFrame, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, map_sub]
  abel

/-- The route-oriented source owner after the raw frame terms have cancelled. -/
noncomputable def sourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  -sourceGramResponse owner lambda family

theorem sourceCycledBandResponse_eq_sourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceCycledBandResponse owner lambda family =
      sourceBandGramResponse owner lambda family := by
  exact sourceCycledBandResponse_eq_neg_sourceGramResponse owner lambda family

/-- The only legal Gate 3L/3U candidate: one completed fixed commutator followed
by the ordered Euler coframe. -/
theorem sourceBandGramResponse_eq_completedCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
        sourceBoundaryCommutator owner lambda ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family := by
  rw [sourceBandGramResponse, sourceGramResponse_eq_fixedCommutator]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, neg_neg]

/-- The same owner with the outer, second-support, reflected-outer, and
prolate branches still recombined. -/
theorem sourceBandGramResponse_eq_neg_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      -((sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda)
          (detectorOperator owner) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family) := by
  rw [sourceBandGramResponse, sourceGramResponse_eq_threeBranch]

end CCM24FiniteSBandTrace
end CCM25Concrete
end Source
end ConnesWeilRH
