/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalCausalDualFrameCorner

/-!
# Causal completed-prolate bracket for the finite-S Gate target

The causal dual-frame corner has the source complement `I - R_0` between the
forward Euler transport and the compact root.  This module rewrites that
complement through the actual CCM24 pair of support projections:

`R_0 = E Q_0 E - K_prol`.

The outer crossing and the second-support/prolate expression remain one
completed bracket.  The result is an operator identity only; it supplies no
uniform estimate and does not split the terms for separate norm bounds.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalCausalCompletedBracket

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCausalSupport
open CCM24FiniteSBandTrace
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSGatePhysicalCausalDualFrameCorner
open CCM24FiniteSGatePhysicalMetricDetectorCorner
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The source band written through the coupled Fourier/prolate identity.
This is one completed operator, not three independently estimable terms. -/
noncomputable def sourceCausalCompletedBand (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda -
    radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
      radialSupportProjection lambda + sourceProlateRemainder lambda

/-- The completed Fourier/prolate bracket is exactly the source quotient band
`E - R_0`. -/
theorem sourceCausalCompletedBand_eq_sourceBandProjection
    (lambda : CCM24SoninScale) :
    sourceCausalCompletedBand lambda = sourceBandProjection lambda := by
  unfold sourceCausalCompletedBand sourceBandProjection
  rw [sourceSoninProjection_eq_compression_sub_prolate]
  abel

/-- The source-Sonin complement is the outer complement plus the completed
Fourier/prolate band.  This is a decomposition identity, not a license to
estimate either summand before the compact root has acted. -/
theorem sourceSoninComplementProjection_eq_radialComplement_add_causalCompletedBand
    (lambda : CCM24SoninScale) :
    sourceSoninComplementProjection lambda =
      radialComplementProjection lambda + sourceCausalCompletedBand lambda := by
  rw [sourceCausalCompletedBand_eq_sourceBandProjection]
  unfold sourceSoninComplementProjection radialComplementProjection
    sourceBandProjection
  abel

/-- The actual causal transport of the complete source complement.  The first
term is the outer crossing; the second is the still-coupled Fourier/prolate
band. -/
noncomputable def finiteEulerCausalCompletedSoninComplement
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L finiteEulerTransportOperator family ∘L
      radialComplementProjection lambda +
    finiteEulerTransportOperator family ∘L sourceCausalCompletedBand lambda

/-- Causality absorbs the completed source band after transport, so the
displayed outer-plus-Fourier/prolate bracket is exactly `E T_S (I-R_0)`. -/
theorem finiteEulerCausalCompletedSoninComplement_eq_causalTransportComplement
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerCausalCompletedSoninComplement lambda family =
      radialSupportProjection lambda ∘L finiteEulerTransportOperator family ∘L
        sourceSoninComplementProjection lambda := by
  have hBandSupport : radialSupportProjection lambda ∘L
      sourceCausalCompletedBand lambda = sourceCausalCompletedBand lambda := by
    rw [sourceCausalCompletedBand_eq_sourceBandProjection]
    exact radialSupportProjection_comp_sourceBandProjection_eq_self lambda
  apply ContinuousLinearMap.ext
  intro u
  have hBandSupportAt := DFunLike.congr_fun hBandSupport u
  simp only [ContinuousLinearMap.comp_apply] at hBandSupportAt
  have hCausalAt := DFunLike.congr_fun
    (radialSupportProjection_comp_transport_comp_self lambda family)
    (sourceCausalCompletedBand lambda u)
  simp only [ContinuousLinearMap.comp_apply] at hCausalAt
  rw [hBandSupportAt] at hCausalAt
  have hComplementAt := DFunLike.congr_fun
    (sourceSoninComplementProjection_eq_radialComplement_add_causalCompletedBand
      lambda) u
  simp only [ContinuousLinearMap.add_apply] at hComplementAt
  simp only [finiteEulerCausalCompletedSoninComplement,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [hComplementAt]
  simp only [map_add]
  rw [hCausalAt]

/-- The literal Gate target is one causal completed-prolate bracket followed
by the compact root.  The rightmost root remains after the full bracket. -/
theorem finiteEulerTargetCommutatorResponse_eq_causalCompletedProlateRootCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      (finiteEulerDualFrame lambda family)† ∘L
        finiteEulerCausalCompletedSoninComplement lambda family ∘L
          (rootConvolution owner)† ∘L rootConvolution owner ∘L
            sourceInclusion lambda := by
  rw [finiteEulerTargetCommutatorResponse_eq_causalDualFrameRootCorner]
  apply ContinuousLinearMap.ext
  intro u
  let z : finiteSCarrier :=
    (ContinuousLinearMap.adjoint (rootConvolution owner))
      (rootConvolution owner (sourceInclusion lambda u))
  have hCompleted := DFunLike.congr_fun
    (finiteEulerCausalCompletedSoninComplement_eq_causalTransportComplement
      lambda family) z
  simp only [ContinuousLinearMap.comp_apply] at hCompleted
  simpa only [z, ContinuousLinearMap.comp_apply] using
    congrArg ((finiteEulerDualFrame lambda family)†) hCompleted.symm

end CCM24FiniteSGatePhysicalCausalCompletedBracket
end CCM25Concrete
end Source
end ConnesWeilRH
