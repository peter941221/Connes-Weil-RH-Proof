# Proof 556: raw local cofactor bridge

Result: the raw adjacent four-term row is exactly the adjoint local raw
cofactor after the reverse transition is cancelled. This is a genuine
same-object operator identity, but it does not provide the family-uniform
Gate 3U estimate.

## Source

The Lean source is
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawLocalCofactor.lean`.
The focused audit is
`ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawLocalCofactorAudit.lean`.

Write `T = T_(p,S)`, `U = U_(p,S)`, `rho = rho_p`, and
`R_S = suffixActualBandRawQuadraticCycledResponse owner lambda S`. The
existing definitions are

```text
RawRow(p,S)† = T R_S - R_(p::S) T
LocalRawDefect(p,S) = rho R_(p::S) - T R_S U.
```

The existing reverse-transition theorem gives

```text
U T = rho I.
```

Therefore the exact calculation is

```text
LocalRawDefect(p,S) T
  = rho R_(p::S) T - T R_S U T
  = rho (R_(p::S) T - T R_S)
  = -rho RawRow(p,S)†.
```

Lean proves this identity before any norm, trace, or absolute value is
introduced. The row is consequently exposed as the adjoint local cofactor,
with the positive scalar still visible.

## Boundary

This bridge does not factor the local raw defect through the actual
ambient-loss plus moving-boundary Julia analysis column. It therefore does not
close Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`. Proof 554's antiresonant obstruction and Proof
555's signed coframe telescope remain active constraints.

## Verification

The focused audit must report exactly
`[propext, Classical.choice, Quot.sound]` for the three new declarations.
