/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRouteKernelNormalForm

/-!
# Non-polar mismatch normal form

Proof 503 expresses the route/polar ordering residual through the concrete
route/polar kernel.  The first-jet contribution has the opposite orientation.
This module combines them into one same-object defect:

```text
RoutePolarKernel(S) - FirstJetResponse(S)
  = PolarCompression(S) - RawResponse(S),

NonpolarGap(p,S)
  = F_(p,S) Mismatch(S) R_(p,S) - rho_p Mismatch(p::S).
```

The mismatch is kept on the literal source carrier.  No coherence, norm
bound, trace estimate, Gate 3U conclusion, sign statement, or RH premise is
introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSBandTrace
open CCM24FiniteSBiSchurRelative
open CCM24FiniteSGramResponse
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSCompletedJuliaRouteKernelNormalForm
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The same-object mismatch -/

/-- The actual polar compression minus the actual raw quadratic response. -/
noncomputable def suffixActualBandRoutePolarRawMismatchKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixPolarDetectorCompression owner lambda S -
    suffixActualBandRawQuadraticCycledResponse owner lambda S

/-- The mismatch is equally the route/polar kernel minus the first-jet
response.  This is the algebraic bridge between the Proof 503 route owner and
the literal raw response. -/
theorem suffixActualBandRoutePolarRawMismatchKernel_eq_routePolarKernel_sub_firstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandRoutePolarRawMismatchKernel owner lambda S =
      suffixActualBandRoutePolarKernel owner lambda S -
        suffixActualBandFirstJetCycledResponse owner lambda S := by
  rw [suffixActualBandRoutePolarRawMismatchKernel,
    suffixActualBandRoutePolarKernel,
    suffixActualBandRawQuadraticCycledResponse,
    suffixActualBandEndpointCycledResponse_eq_base_sub_routeTarget]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel_nf

/-! ## Its local relative defect -/

/-- The one-step relative defect of the polar/raw mismatch. -/
noncomputable def suffixActualBandLocalRoutePolarRawMismatchDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandRoutePolarRawMismatchKernel owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S -
    (primeSchurMarkovScalar p : ℂ) •
      suffixActualBandRoutePolarRawMismatchKernel owner lambda (p :: S)

/-- The Proof 502 non-polar gap is exactly the relative defect of the single
polar/raw mismatch kernel. -/
theorem suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalNonpolarLocalizationGap owner lambda p S =
      suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S := by
  rw [suffixActualBandLocalNonpolarLocalizationGap,
    suffixActualBandLocalFirstJetContribution,
    suffixActualBandLocalRoutePolarOrderingResidual_eq_kernel_relativeDefect,
    suffixActualBandLocalRoutePolarRawMismatchDefect]
  simp only [suffixActualBandRoutePolarRawMismatchKernel_eq_routePolarKernel_sub_firstJet]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub, smul_sub]
  abel_nf

/-! ## Two-term signed readback -/

/-- The complete local raw defect is the polar Julia defect plus the single
polar/raw mismatch defect. -/
theorem suffixActualBandLocalRawDefect_eq_polarJulia_add_routePolarRawMismatchDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRawDefect owner lambda p S =
      suffixActualBandLocalPolarJuliaContribution owner lambda p S +
        suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S := by
  rw [suffixActualBandLocalRawDefect_eq_polarJulia_add_nonpolarGap,
    suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect]

end CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH
