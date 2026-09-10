# G8 P1 visible-boundary prefix limit (2026-09-11)

## Result

`C1G8P1FinitePrimePrefixLimit.lean` proves the operator identity
`g8VisibleBoundaryOperator_eq_arithmeticOperator`: the selected visible Euler
boundary assembly built from `familyVisiblePrimePowerTerms family` is exactly
the existing arithmetic operator for the same `FinitePrimePowerFamily`.

It then transports the existing finite-prefix trace convergence theorem to the
visible-boundary owner:

```text
Tr(prefix_N visible-boundary assembly)
  → ∑ finitePrimeTerm(p^m).
```

The proof keeps the original support interval, named basis, and per-term
`GlobalPrimePowerTraceBasisData` explicit.

## Scope and status

This is FORMAL P1 arithmetic-prefix evidence.  It concerns the visible Euler
assembly only.  It does not prove that the physical metric cutoff operator is
that assembly, does not produce the same-owner remainder limit, and does not
prove P2 or P3.

## Verification

Owning and audit targets were built in
`1410_g8_finite_prime_prefix_limit.log`: success footer for 3300 jobs, zero
`error:` and `sorryAx`, and both audited declarations have exactly
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
