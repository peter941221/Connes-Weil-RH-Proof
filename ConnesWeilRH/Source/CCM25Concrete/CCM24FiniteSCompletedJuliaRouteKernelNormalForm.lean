/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaSignedLocalization

/-!
# Route/polar kernel normal form

Proof 502 isolates the non-polar localization gap as the first jet plus an
ordering residual.  This module expands that residual one level further.  The
route endpoint uses the unpolarized frame and its ordered Gram correction,
whereas the Schur--Markov numerator uses the adjacent polar compression.  Their
difference is the relative defect of one concrete route/polar kernel:

```text
K_S = baseDetector + polarCompression(S) - routeTarget(S),

OrderingResidual(p,S)
  = F_(p,S) K_S R_(p,S) - rho_p K_(p::S).
```

Thus vanishing of the ordering residual is equivalent to an explicit adjacent
coherence equation.  No such coherence is assumed here, and no Gate 3U, sign,
or RH conclusion is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRouteKernelNormalForm

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSBandTrace
open CCM24FiniteSBiSchurRelative
open CCM24FiniteSGramResponse
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Concrete route target and base responses -/

/-- The route-ordered target response before the endpoint subtraction. -/
noncomputable def suffixActualBandRouteTargetResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixActualBandTargetFrameRootLeg owner lambda S)† ∘L
    suffixActualBandTargetDualRootLeg owner lambda S

/-- The fixed base detector response used by every route endpoint. -/
noncomputable def suffixActualBandBaseDetectorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : SourceOp lambda :=
  (actualBandBaseRootLeg owner lambda)† ∘L actualBandBaseRootLeg owner lambda

/-- The endpoint is exactly base response minus the route target response. -/
theorem suffixActualBandEndpointCycledResponse_eq_base_sub_routeTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandEndpointCycledResponse owner lambda S =
      suffixActualBandBaseDetectorResponse owner lambda -
        suffixActualBandRouteTargetResponse owner lambda S := by
  rfl

/-! ## Route/polar kernel -/

/-- The concrete kernel carrying the mismatch between the polar compression and
the route-ordered Gram target. -/
noncomputable def suffixActualBandRoutePolarKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandBaseDetectorResponse owner lambda +
      suffixPolarDetectorCompression owner lambda S -
    suffixActualBandRouteTargetResponse owner lambda S

/-- The local ordering residual is the relative defect of the route/polar
kernel.  This is an operator identity before any trace or norm. -/
theorem suffixActualBandLocalRoutePolarOrderingResidual_eq_kernel_relativeDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRoutePolarOrderingResidual owner lambda p S =
      suffixEulerFrameTransition lambda p S ∘L
          suffixActualBandRoutePolarKernel owner lambda S ∘L
            suffixEulerFrameReverseTransition lambda p S -
        (primeSchurMarkovScalar p : ℂ) •
          suffixActualBandRoutePolarKernel owner lambda (p :: S) := by
  rw [suffixActualBandLocalRoutePolarOrderingResidual,
    suffixEulerDetectorRelativeNumerator, relativeNumerator,
    primeSchurMarkovScaleOperator,
    suffixActualBandLocalRouteEndpointDefect,
    suffixActualBandEndpointCycledResponse_eq_base_sub_routeTarget,
    suffixActualBandRoutePolarKernel]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandRoutePolarKernel,
    suffixActualBandBaseDetectorResponse, suffixActualBandRouteTargetResponse,
    suffixActualBandEndpointCycledResponse,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_add, map_smul, smul_sub,
    smul_add]
  abel_nf

/-- The non-polar gap is the first jet plus the relative defect of the concrete
route/polar kernel. -/
theorem suffixActualBandLocalNonpolarLocalizationGap_eq_firstJet_add_kernelDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalNonpolarLocalizationGap owner lambda p S =
      suffixActualBandLocalFirstJetContribution owner lambda p S +
        (suffixEulerFrameTransition lambda p S ∘L
            suffixActualBandRoutePolarKernel owner lambda S ∘L
              suffixEulerFrameReverseTransition lambda p S -
          (primeSchurMarkovScalar p : ℂ) •
            suffixActualBandRoutePolarKernel owner lambda (p :: S)) := by
  rw [suffixActualBandLocalNonpolarLocalizationGap,
    suffixActualBandLocalRoutePolarOrderingResidual_eq_kernel_relativeDefect]

/-! ## Exact coherence target -/

/-- The ordering residual vanishes exactly when the concrete route/polar kernel
obeys the adjacent Schur--Markov coherence equation. -/
theorem suffixActualBandLocalRoutePolarOrderingResidual_eq_zero_iff_kernel_coherent
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRoutePolarOrderingResidual owner lambda p S = 0 ↔
      suffixEulerFrameTransition lambda p S ∘L
          suffixActualBandRoutePolarKernel owner lambda S ∘L
            suffixEulerFrameReverseTransition lambda p S =
        (primeSchurMarkovScalar p : ℂ) •
          suffixActualBandRoutePolarKernel owner lambda (p :: S) := by
  rw [suffixActualBandLocalRoutePolarOrderingResidual_eq_kernel_relativeDefect]
  exact sub_eq_zero

end CCM24FiniteSCompletedJuliaRouteKernelNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH
