/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionTraceLedger
import ConnesWeilRH.Dev.C1CrossingEulerLogReadback
import ConnesWeilRH.Dev.C1CrossingCommonCarrier
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# C1 Stage-3 carrier readback (active namespace) — Gate 2 arithmetic side

The carrier-side ledger (`C1Stage3ProjectionTraceLedger`) proves, for an arbitrary
finite prime-power set `terms`, that the ordinary trace of the projection response splits as

```text
Tr(projectionResponse owner λ S) = (∑_{pm ∈ terms} finitePrimeTerm(pm)) + Tr(sameObjectResidual)
```

This module pins that arithmetic side to a **clean real scalar** by instantiating
`terms := canonicalPrimePowerTerms owner` — the unique finite prime-power support of the
compact-log test — and chaining the existing Stage-2 Euler-log readback
(`C1CrossingEulerLogReadback`).  The result is, for any selected Weil-square `owner`,

```text
Re Tr(projectionResponse owner λ S)
    = (∑_{n ∈ globalPrimeIndexSet} finitePrimeTermReal n)   -- the real carrier arithmetic side
      + Re Tr(sameObjectResidual owner λ S canonicalTerms)  -- Gate 3 target, isolated
```

This is pure assembly of already-proved pieces: no new analytic estimate, positivity claim, or
sign assumption.  It is the concrete first half of doc-1039 Gate 2 (the exact trace ledger whose
arithmetic side reads back to `qw g`); the residual's vanishing limit and its unification with
the closed vertical pole/archimedean ledgers remain the subsequent rounds.

Firewall: imports only active C1 modules (`C1Stage3ProjectionTraceLedger`,
`C1CrossingEulerLogReadback`) plus shared source bricks — **no** frozen route leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3CarrierReadback

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.SelectedWeilSquare
open C1Stage3ProjectionTraceLedger
open C1CrossingCommonCarrier
open C1CrossingEulerLogReadback
open scoped BigOperators

noncomputable section

/-- The real arithmetic carrier sum over the owner's canonical finite prime-power support.  This
is exactly the `.re` of the projection-response ledger's arithmetic side (see below), and it is
the scalar that downstream reads back to `C1SameOwnerWeil.finitePrimeSum`. -/
noncomputable def selectedArithmeticCarrierSum (owner : SelectedWeilSquareOwner) : ℝ :=
  ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
    owner.finitePrimeTermReal n

/-- Gate-2 arithmetic readback: with the ledger's prime-power set instantiated at the canonical
support, the real part of the projection-response trace equals the clean carrier scalar plus the
residual's real trace.  The residual is `sameObjectResidual` evaluated on the same canonical
terms — every still-unproved finite-S effect stays isolated there (Gate 3). -/
theorem stage3CarrierReadback_arithmetic_eq_selectedRealSum_residual
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous a c (canonicalCrossingLengthSet owner))
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ canonicalPrimePowerTerms owner},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
       (projectionResponse owner lambda S)).re =
      selectedArithmeticCarrierSum owner +
        (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda S (canonicalPrimePowerTerms owner))).re := by
  have hledger : CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
       (projectionResponse owner lambda S) =
      (∑ pm ∈ canonicalPrimePowerTerms owner, owner.finitePrimeTerm (pm.1 ^ pm.2)) +
        CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda S (canonicalPrimePowerTerms owner)) :=
    stage3TraceLedger_projectionResponse_eq_finitePrimeSum_add_residual
      owner a c lambda S (canonicalPrimePowerTerms owner)
      (fun pm hpm => canonicalPrimePowerTerms_prime owner hpm)
      (fun pm hpm => canonicalPrimePowerTerms_exponent_ne_zero owner hpm)
      hsupp globalBasis basisData hresponse
  have heq_selected :
      (∑ pm ∈ canonicalPrimePowerTerms owner,
        eulerLogWeightedCarrierPairTrace data pm.1 pm.2).re = selectedArithmeticCarrierSum owner :=
    canonicalEulerLogCarrierPairTrace_sum_re_eq_selectedFinitePrimeTerm_sum
      owner a c data hsupp
  have hprime_re :
      (∑ pm ∈ canonicalPrimePowerTerms owner, owner.finitePrimeTerm (pm.1 ^ pm.2)).re =
        selectedArithmeticCarrierSum owner := by
    -- Pointwise equality of the two finite sums as complex numbers: each prime-power term is
    -- exactly the Euler-log carrier pair trace at that crossing length (Stage-2 identity).
    have hsum_eq : ∑ pm ∈ canonicalPrimePowerTerms owner, owner.finitePrimeTerm (pm.1 ^ pm.2) =
        ∑ pm ∈ canonicalPrimePowerTerms owner, eulerLogWeightedCarrierPairTrace data pm.1 pm.2 := by
      apply Finset.sum_congr rfl
      intro pm hpm
      exact (eulerLogWeightedCarrierPairTrace_eq_finitePrimeTerm_pow owner a c
          (canonicalCrossingLengthSet owner) data
          (canonicalPrimePowerTerms_prime owner hpm)
          (canonicalPrimePowerTerms_exponent_ne_zero owner hpm)
          hsupp (canonicalCrossingLength_mem owner hpm)).symm
    rw [hsum_eq]
    exact heq_selected
  rw [hledger]
  simp only [Complex.add_re, hprime_re]

end
end C1Stage3CarrierReadback
end Source
end ConnesWeilRH
