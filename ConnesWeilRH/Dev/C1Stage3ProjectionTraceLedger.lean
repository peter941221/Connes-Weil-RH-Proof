/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24SemilocalFourierSupport
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# C1 Stage-3 projection-trace ledger (active namespace) — Gate 2 carrier side

Gate 2 of the Stage-3 admission spec (`docs/proofs/1039`) needs a same-owner trace
ledger whose arithmetic side reads back to `C1SameOwnerWeil.qw g`.  This module
re-exposes, in the **active C1 namespace** and from **shared source bricks only**,
the exact ledger identity:

```text
Tr(projectionResponse)
  = (∑_{p^m ∈ terms} finitePrimeTerm(p^m))   -- arithmetic side → finite prime sum
    + Tr(sameObjectResidual)                 -- Gate 3 target (→ 0, no sign assumed)
```

The detector is the positive whole-line convolution operator `(conv h)† ∘ conv h`;
the CCM24 side it acts on is the Sonin-projection band difference.  Their composition
is the projection response — a genuine same-object operator on `cc20GlobalLogCrossingL2`
(the same space as `stage3ProjectionKernel`).  The arithmetic operator is the selected
finite prime-power crossing-operator sum, whose ordinary trace along any whole-line basis
equals the finite prime-term sum (`SelectedCrossingOperatorBridge`, already proved).

The residual isolates every still-unproved finite-S effect.  Its vanishing limit — without
assuming `qw g ≥ 0` — is **Gate 3**, not Gate 2.  This module proves only the exact
algebraic ledger; it claims no positivity, cutoff limit, or sign.

Firewall (per doc 1039 "re-prove instead of importing the frozen residual ledger"): this
module imports only shared source bricks — `CCM24SemilocalFourierSupport`,
`HilbertSchmidtIdeal` (for `isTraceClassAlong_sub`), and `SelectedCrossingOperatorBridge`.
**No** frozen route leaf (`*Gate3U*`, `C1LaneR*`,
`C1XiCenterTwoGamma*`) is pulled in as a consumer.  It is the active-namespace re-prove of
the minimal algebraic fact, so the Stage-3 producer can live wholly inside active C1.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3ProjectionTraceLedger

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.SelectedWeilSquare
open scoped BigOperators

noncomputable section

/-- The common logarithmic carrier — literally the same Hilbert space as
`stage3ProjectionKernel`, so the ledger and the positive core are same-object. -/
noncomputable abbrev finiteSCarrier := cc20GlobalLogCrossingL2

/-- Common radial-support projection `E_lambda`. -/
noncomputable def radialSupportProjection (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection

/-- Archimedean complete-Sonin projection `R_0`. -/
noncomputable def sourceSoninProjection (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.starProjection

/-- Finite-S complete-Sonin projection `R_S` — the gram-corrected frame operator of the
bounded invertible CCM24 Sonin transport selected by `S`. -/
noncomputable def targetSoninProjection (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  (concreteCCM24SoninTransportData lambda S).gramCorrectedTargetSoninProjection

/-- The Sonin band difference `B_S - B_0 = R_0 - R_S` on the same carrier. -/
noncomputable def soninBandDifference (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda - targetSoninProjection lambda S -
    (radialSupportProjection lambda - sourceSoninProjection lambda)

/-- The genuine positive whole-line convolution detector for the selected Weil square owner. -/
noncomputable def detectorOperator
    (owner : SelectedWeilSquareOwner) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  cc20GlobalConvolutionPositive owner.sourceTest.involution.test

/-- The selected finite prime-power crossing-operator sum — the arithmetic side of the ledger. -/
noncomputable def arithmeticOperator
    (owner : SelectedWeilSquareOwner) (terms : Finset (ℕ × ℕ)) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  eulerLogWeightedGlobalPairTraceOperatorSum owner terms

/-- The projection response: the positive detector applied to the Sonin band difference. -/
noncomputable def projectionResponse
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L soninBandDifference lambda S

/-- The canonical same-object residual: every still-unproved finite-S effect. -/
noncomputable def sameObjectResidual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (terms : Finset (ℕ × ℕ)) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  projectionResponse owner lambda S - arithmeticOperator owner terms

/-- Definitional bookkeeping: the response splits into its arithmetic side plus residual. -/
theorem stage3ProjectionResponse_eq_arithmetic_add_residual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (terms : Finset (ℕ × ℕ)) :
    projectionResponse owner lambda S =
      arithmeticOperator owner terms + sameObjectResidual owner lambda S terms := by
  rw [sameObjectResidual]
  abel

/-- Gate 2 carrier-side ledger: the ordinary trace of the projection response along any
whole-line basis equals the finite prime-term sum plus the residual trace.  The first
summand is the existing selected crossing-operator readback; every still-unproved finite-S
effect sits in `sameObjectResidual` (Gate 3's target). -/
theorem stage3TraceLedger_projectionResponse_eq_finitePrimeSum_add_residual
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (projectionResponse owner lambda S) =
      (∑ pm ∈ terms, owner.finitePrimeTerm (pm.1 ^ pm.2)) +
        CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda S terms) := by
  have harith_tc : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (arithmeticOperator owner terms) := by
    rw [arithmeticOperator]
    exact eulerLogWeightedGlobalPairTraceOperatorSum_isTraceClassAlong
      owner a c terms hprime hsupp globalBasis basisData
  have hres_tc : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (sameObjectResidual owner lambda S terms) :=
    isTraceClassAlong_sub globalBasis _ _ hresponse harith_tc
  rw [stage3ProjectionResponse_eq_arithmetic_add_residual owner lambda S terms]
  have hadd : CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (arithmeticOperator owner terms + sameObjectResidual owner lambda S terms) =
      CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (arithmeticOperator owner terms) +
        CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda S terms) :=
    ordinaryTraceAlong_add globalBasis _ _ harith_tc hres_tc
  rw [hadd]
  have harith_sum : CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (arithmeticOperator owner terms) =
      ∑ pm ∈ terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
    rw [arithmeticOperator]
    exact ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
      owner a c terms hprime hnonzero hsupp globalBasis basisData
  rw [harith_sum]

end
end C1Stage3ProjectionTraceLedger
end Source
end ConnesWeilRH
