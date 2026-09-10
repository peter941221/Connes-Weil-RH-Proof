# G8 P2 canonical visible-Euler residual (2026-09-11)

## Result

`C1G8P2CanonicalResidual.lean` defines the G8 residual as the existing
same-owner operator `sameObjectResidual owner lambda family`.  The theorem
`projectionResponse_eq_g8VisibleBoundary_add_residual` rewrites the physical
projection response as

```text
projectionResponse = visible Euler boundary assembly + canonical residual.
```

The theorem
`ordinaryTraceAlong_projectionResponse_eq_g8VisibleBoundary_sum_add_residual`
gives the corresponding named-basis trace identity, with the visible assembly
read back to the finite prime-power sum.

## Scope and status

This is FORMAL P2 identity/consumer evidence.  The residual is not an
externally chosen scalar and remains on the same finite-S owner.  No theorem
here proves that its trace tends to zero, proves the exact Weil limit, or gives
the P2 sign inequality; P3 also remains open.

## Verification

Owning and audit targets were built in
`1414_g8_p2_canonical_residual.log`: success footer for 3301 jobs, zero
`error:` and `sorryAx`, and all three audited declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
