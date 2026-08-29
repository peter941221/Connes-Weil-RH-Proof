/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1Stage3ProjectionTraceLedger

/-!
# C1 selected-detector semi-local Euler residual

The active Stage-3 ledger formerly names its arithmetic operator by a finite
set of natural-number prime powers.  The Euler-boundary brick shows that the
same finite sum is a literal sum of radial semi-local boundary crossings owned
by a visible-place list `S`.  This module moves the residual to that concrete
Euler owner:

```text
projection response = visible Euler boundary sum + Euler residual.
```

The equality is exact and preserves the earlier residual after the visible
place proofs are erased.  It deliberately makes no finite-part, convergence,
positivity, or RH claim: those are the remaining semi-local mathematical
obligations, now isolated against a genuine Euler boundary rather than an
externally supplied arithmetic operator.

Firewall: both imports are active C1/shared-source leaves.  No frozen
`*Gate3U*`, `*RouteA*`, `*RawRenewal*`, `C1LaneR*`, or
`C1XiCenterTwoGamma*` consumer is imported.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SelectedDetectorSemiLocalResidual

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.SelectedWeilSquare
open C1SelectedDetectorSemiLocalEulerBoundary
open C1Stage3ProjectionTraceLedger
open scoped BigOperators

noncomputable section

/-- The residual of the actual finite visible Euler boundary inside the
same `projectionResponse` owner. -/
noncomputable def selectedEulerBoundaryResidual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (data : VisiblePrimePowerTerms S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  projectionResponse owner lambda S -
    selectedEulerLogBoundaryPairOperatorSum owner data

/-- The literal visible Euler-boundary sum is exactly the old arithmetic
operator after forgetting only visible-place proof fields. -/
theorem selectedEulerBoundarySum_eq_arithmeticOperator
    (owner : SelectedWeilSquareOwner) {S : List CCM24VisiblePrime}
    (data : VisiblePrimePowerTerms S) :
    selectedEulerLogBoundaryPairOperatorSum owner data =
      arithmeticOperator owner data.natTerms := by
  rw [selectedEulerLogBoundaryPairOperatorSum_eq_crossingOperatorSum]
  rfl

/-- The concrete Euler residual is the earlier same-object residual, with no
analytic approximation or trace argument hidden in the conversion. -/
theorem selectedEulerBoundaryResidual_eq_sameObjectResidual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (data : VisiblePrimePowerTerms S) :
    selectedEulerBoundaryResidual owner lambda S data =
      sameObjectResidual owner lambda S data.natTerms := by
  rw [selectedEulerBoundaryResidual, sameObjectResidual,
    selectedEulerBoundarySum_eq_arithmeticOperator]

/-- Exact same-owner bookkeeping with the geometric Euler boundary as the
arithmetic summand. -/
theorem projectionResponse_eq_selectedEulerBoundary_add_residual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (data : VisiblePrimePowerTerms S) :
    projectionResponse owner lambda S =
      selectedEulerLogBoundaryPairOperatorSum owner data +
        selectedEulerBoundaryResidual owner lambda S data := by
  rw [selectedEulerBoundaryResidual]
  abel

/-- The Euler residual is trace-class whenever the response is trace-class:
the finite visible boundary summand supplies the second trace-class leg. -/
theorem selectedEulerBoundaryResidual_isTraceClassAlong
    (owner : SelectedWeilSquareOwner) (a c : ℝ) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (data : VisiblePrimePowerTerms S)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ data.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    IsTraceClassAlong globalBasis
      (selectedEulerBoundaryResidual owner lambda S data) := by
  apply isTraceClassAlong_sub globalBasis _ _ hresponse
  exact selectedEulerLogBoundaryPairOperatorSum_isTraceClassAlong
    owner a c data hsupp globalBasis basisData

/-- The trace ledger now reads the projection response against a literal
finite visible Euler boundary.  The residual is retained explicitly; this is
not a positivity or finite-part conclusion. -/
theorem ordinaryTraceAlong_projectionResponse_eq_visibleEulerSum_add_residual
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (data : VisiblePrimePowerTerms S)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ data.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    ordinaryTraceAlong globalBasis (projectionResponse owner lambda S) =
      (∑ pm ∈ data.terms, owner.finitePrimeTerm (pm.1.1 ^ pm.2)) +
        ordinaryTraceAlong globalBasis
          (selectedEulerBoundaryResidual owner lambda S data) := by
  have hboundary : IsTraceClassAlong globalBasis
      (selectedEulerLogBoundaryPairOperatorSum owner data) :=
    selectedEulerLogBoundaryPairOperatorSum_isTraceClassAlong
      owner a c data hsupp globalBasis basisData
  have hresidual : IsTraceClassAlong globalBasis
      (selectedEulerBoundaryResidual owner lambda S data) :=
    selectedEulerBoundaryResidual_isTraceClassAlong
      owner a c lambda S data hsupp globalBasis basisData hresponse
  rw [projectionResponse_eq_selectedEulerBoundary_add_residual]
  rw [ordinaryTraceAlong_add globalBasis _ _ hboundary hresidual]
  rw [ordinaryTraceAlong_selectedEulerLogBoundaryPairOperatorSum_eq_finitePrimeTerm_sum
    owner a c data hsupp globalBasis basisData]

end
end C1SelectedDetectorSemiLocalResidual
end Source
end ConnesWeilRH
