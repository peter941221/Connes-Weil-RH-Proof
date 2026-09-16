# 1529 — Actual outer-pair radial-leakage consumer

Date: 2026-09-17

The arbitrary-support calculation in record 1528 remains a genuine warning:
for an unconstrained Fourier factor `Q`, the outer plus reflected outer pair
expands to four noncommuting terms.  The actual healthy `CompactLog` ledger has
additional structure, however.  Its Fourier-support projection fixes the
source inclusion, formally proved as
`sourceFourierSupportProjection_comp_sourceInclusion_eq_self`:
`Q ∘L J = J`.

Substitution into the exact expansion gives the checked identity

```text
(outer(E,Q,M) + reflectedOuter(E,Q,M)) ∘L J
  = -(E ∘L Q ∘L (id - E) ∘L M ∘L J)
    - ((id - E) ∘L M ∘L J).
```

The new theorem
`sourceSoninOuterPair_sourceBasis_normSq_summable_of_radialLeakage` then uses
`PositiveTrace.summable_normSq_postcomp` and
`PositiveTrace.summable_normSq_add` to prove the complete source-basis
square-sum after an arbitrary bounded ambient postcomposition `D` and a
source-side precomposition `N`, assuming only

```text
Summable (fun i => ||((id - E) ∘L M ∘L J ∘L N) (e_i)||^2).
```

This is a formal consumer and an exact reduction of the outer-pair part of
WO-B.  It supplies no analytic bound for the raw leakage of the actual finite
visible-prime boundary factors.  The status therefore stays WO-B OPEN; the
remaining target is now one explicit leakage square-sum per physical factor.

Owning declaration: `ConnesWeilRH.Dev.C1G8R3BoundaryOutputFactorizationBridge`.
Audit: `...BoundaryOutputFactorizationBridgeAudit`.
