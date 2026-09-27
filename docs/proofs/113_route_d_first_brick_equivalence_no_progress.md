# 113 — Route D first brick is equivalent to the original sign target

Date: 2026-09-27.

Status: scoped no-progress result. The proposed Route-D defect domination is
not a smaller obligation under the current corrected trace interface. This
does not rule out a genuinely new owner-specific identity, but it freezes the
current factorization sketch.

## Starting identities

Use the project-recorded definitions, conditional on the trace-class,
cyclicity, and same-owner readback hypotheses in proof record 016:

```text
H = 2P - I
P_hat = U^*(I-P)U
T = U^* H U - H

P T P = -2 P P_hat P

PositiveTrace = Tr(X P P_hat P)
D             = (1/2) Tr(X (T - P T P))
```

Here `X = theta_S(F_g)` is the actual square operator for the selected
detector. No replacement test or fixed-prime owner is introduced.

## Reduction

Substitute `P T P = -2 P P_hat P` into the defect:

```text
D
  = (1/2) Tr(X T) + Tr(X P P_hat P)
  = (1/2) Tr(X T) + PositiveTrace.
```

Therefore the proposed Route-D domination is exactly:

```text
D <= PositiveTrace
  <=> (1/2) Tr(X T) <= 0.
```

The corrected trace identity identifies the same quantity with the Weil
functional (up to the already-separated pole term):

```text
QW(g,g) = PositiveTrace - D
         = -(1/2) Tr(X T).
```

Hence:

```text
D <= PositiveTrace
  <=> QW(g,g) >= 0
  <=> ICgate(g.square) <= 0
```

under the existing same-owner P2 readback.

## Decision

The proposed contraction inequality is not a new lower obligation. Unless an
independently constructed `C` is supplied together with a proof of
`0 <= C <= I` from actual finite-S arithmetic data, the factorization merely
renames the producer premise.

```text
ROUTE-D-CURRENT-FIRST-BRICK: NO PROGRESS / FREEZE
```

Scope:

```text
rejected: the current abstract defect-domination target;
still open: a genuinely new owner-specific arithmetic identity that proves
the same sign without assuming the sign in the definition of C.
```

No Lean consumer, parameter scan, or producer assembly is licensed.

Evidence:

- `docs/proofs/016_corrected_trace_identity.md`
- `docs/map/108_route_d_theta_supersymmetric_defect_domination.md`
- `docs/proofs/112_route_d_universal_contraction_no_go.md`
