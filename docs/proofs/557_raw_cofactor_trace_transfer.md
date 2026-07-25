# Proof 557: raw cofactor trace transfer

Result: the existing fixed-suffix Hilbert--Schmidt owner of the local raw
defect transfers through the bounded Euler transition to the raw four-term
row. This closes fixed-S trace legality for the row under an explicit pair
owner, but it does not prove a family-uniform Gate 3U bound.

## Exact mechanism

Let `T = T_(p,S)`, `U = U_(p,S)`, and `rho = rho_p`. Proof 556 gives

```text
LocalRawDefect(p,S) T = -rho RawRow(p,S)†.
```

Given a `BasisHilbertSchmidtPairData` whose trace product is the local raw
defect, the existing bounded-sandwich owner proves that
`LocalRawDefect(p,S) T` is trace class. Since `rho != 0`, Lean solves the
cofactor:

```text
RawRow(p,S)†
  = (-rho⁻¹) • (LocalRawDefect(p,S) T).
```

Adjoint closure then proves `RawRow(p,S)` is trace class in the same source
basis. The ordinary trace readback is kept in the legal orientation:

```text
Tr(RawRow(p,S))
  = star((-rho⁻¹) * Tr(LocalRawDefect(p,S) T)).
```

No unrestricted cyclicity is used to replace `Tr(LocalRawDefect T)` by the
trace of the local defect itself.

The concrete wrapper
`ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_of_actual_owner`
now packages the existing finite-window pair owner and the nested target
Hilbert basis. This removes the carrier mismatch between the one boundary
pair basis used to build the pair data and the two-pair target space used by
the final bounded sandwich.

The target-side readback is also exposed without hiding the target basis:
`ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_targetTrace_actual`
accepts an explicit basis of the nested carrier and proves

```text
Tr(RawRow(p,S))
  = star((-rho_p^-1) *
      Tr_target((right(p,S) * T_(p,S)) * left(p,S)^dagger)).
```

This uses the genuine Hilbert--Schmidt cyclic theorem and the square-summability
transfer for bounded precomposition. The target trace is an ordered cross
trace; it is not the trace of the local defect alone.

The generic theorem `ordinaryTraceAlong_l2Sum_targetTrace_eq_add` then splits
a combined target cross trace into the two component target traces. The proof
first cycles the combined `l2Sum` owner back to the source carrier, applies
the exact `l2Sum_traceProduct_eq_add` identity, and cycles each component
separately. This preserves the signed channel structure and does not assert
that the off-diagonal product blocks vanish as operators.

The ordered-difference theorem
`ordinaryTraceAlong_l2Sum_boundedTargetTrace_eq_scalar_orderedDifference`
keeps the forward and reverse maps in their actual order. Given
`reverse * forward = scalar * I`, it proves

```text
Tr_target(combined cross trace)
  = scalar * (Tr(new * forward) - Tr(forward * old)).
```

The two source compositions are intentionally different. No commutation of
`forward` through the old response is used.

The actual-owner theorem
`ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_targetTrace_eq_orderedDifference`
instantiates this identity with the repository's raw suffix pair owners. It
reads the target trace back to

```text
rho_p * (Tr(RawResponse(p :: S) * T_(p,S))
       - Tr(T_(p,S) * RawResponse(S))).
```

This is the first actual source readback of the target-side cofactor. It keeps
the two response compositions ordered and signed; it does not estimate them
separately.

## Source and audit

Source:
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawCofactorTrace.lean`

Audit:
`ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawCofactorTraceAudit.lean`

## Boundary

This is fixed-S trace bookkeeping. It supplies no uniform bound on the
cofactor, no factorization through the actual ambient-loss plus moving-
boundary Julia analysis column, no finite-S sign, no Burnol identity, and no
RH proof.
