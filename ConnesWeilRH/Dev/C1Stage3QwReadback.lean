/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3CarrierReadback
import ConnesWeilRH.Dev.C1Stage3ProjectionTraceLedger
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1 Stage-3 `qw` readback (active namespace) — Gate 2 full wiring, arithmetic+vertical side

The carrier ledger (`C1Stage3CarrierReadback`) pins the real part of the projection-response
trace to a clean real scalar plus the canonical residual:

```text
Re Tr(projectionResponse owner λ S) = selectedArithmeticCarrierSum owner + Re Tr(sameObjectResidual …)
```

and `selectedArithmeticCarrierSum owner` is exactly the finite prime-power sum of the selected
Weil square.  This module closes Gate 2's readback by combining that identity with the exact
decomposition of the same-owner Weil value (`C1SameOwnerWeil`) into its pole, archimedean, and
finite-prime terms:

```text
qw g = pole(g*∗g) − arch(g*∗g) − finitePrimeSum(g*∗g)
     = owner.poleTerm.re − owner.archimedeanTerm.re − selectedArithmeticCarrierSum owner
```

Substituting the carrier readback for `selectedArithmeticCarrierSum owner` gives, for any route
test `g` (with `owner := ofCompactLogTest g`) and its canonical prime-power support:

```text
qw g = owner.poleTerm.re − owner.archimedeanTerm.re
      − Re Tr(projectionResponse owner λ S) + Re Tr(sameObjectResidual owner λ S canonicalTerms)
```

This is pure assembly of already-proved pieces (the carrier readback, the `C1SameOwnerWeil`
component bridges, and the definitional equality between the selected finite-prime sum and
`selectedArithmeticCarrierSum`).  No positivity, cutoff-limit, or sign claim is made here; the
residual's vanishing limit remains Gate 3.

Firewall: imports only active C1 modules (`C1Stage3CarrierReadback`, `C1Stage3ProjectionTraceLedger`)
plus `C1SameOwnerWeil` — **no** frozen route leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3QwReadback

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.SelectedWeilSquare
open C1Stage3ProjectionTraceLedger
open C1Stage3CarrierReadback
open C1CrossingCommonCarrier
open C1CrossingEulerLogReadback

noncomputable section

/-- Gate-2 full readback: the same-owner Weil value of `g` equals its pole and archimedean
components minus the real part of the projection-response trace, plus the real part of the
canonical residual.  The finite-prime side is carried inside the response by the carrier ledger;
the still-unproved finite-S effect stays isolated in `sameObjectResidual` (Gate 3). -/
theorem stage3QwReadback_qw_eq_pole_sub_arch_sub_response_add_residual
    (g : CompactLogTest)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (data : CrossingCommonCarrierData g.test g.test.continuous a c
        (canonicalCrossingLengthSet (SelectedWeilSquareOwner.ofCompactLogTest g)))
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ canonicalPrimePowerTerms (SelectedWeilSquareOwner.ofCompactLogTest g)},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
        (projectionResponse (SelectedWeilSquareOwner.ofCompactLogTest g) lambda S)) :
    C1SameOwnerWeil.qw g =
      ((SelectedWeilSquareOwner.ofCompactLogTest g).poleTerm).re -
        ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanTerm).re -
          (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
              (projectionResponse (SelectedWeilSquareOwner.ofCompactLogTest g) lambda S)).re +
            (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
                (sameObjectResidual (SelectedWeilSquareOwner.ofCompactLogTest g) lambda S
                    (canonicalPrimePowerTerms (SelectedWeilSquareOwner.ofCompactLogTest g)))).re := by
  let owner : SelectedWeilSquareOwner := SelectedWeilSquareOwner.ofCompactLogTest g
  -- #12 carrier readback (already green): Re Tr(projectionResponse) = selSum + Re Tr(residual).
  have hresp := stage3CarrierReadback_arithmetic_eq_selectedRealSum_residual
      owner a c lambda S data hsupp globalBasis basisData hresponse
  rw [C1SameOwnerWeil.qw_eq_psi_square g,
      C1SameOwnerWeil.psi_eq_components (g.convolutionSquare)]
  rw [C1SameOwnerWeil.poleTerm_square_eq_selected g]
  rw [C1SameOwnerWeil.archimedeanTerm_square_eq_selected g]
  have hfs : C1SameOwnerWeil.finitePrimeSum (g.convolutionSquare) = selectedArithmeticCarrierSum owner := by
    simpa only [selectedArithmeticCarrierSum, owner] using
      C1SameOwnerWeil.finitePrimeSum_square_eq_selected g
  rw [hfs]
  linarith [hresp]

end
end C1Stage3QwReadback
end Source
end ConnesWeilRH
