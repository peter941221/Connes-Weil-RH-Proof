# 1184 — Residual-aware Bombieri quadratic P2 socket

Date: 2026-09-06

The structure `BombieriQuadraticResidualP2BridgeData` keeps the infinite
spectral-tail correction explicit.  Its owner-changing fields are

```text
qw(g) = Re⟨w,H(Γ;t)w⟩ − residual,
|residual| ≤ tailBound,
tailBound ≤ Re⟨w,H(Γ;t)w⟩.
```

The existing finite Wirtinger theorem supplies nonnegativity of the matrix
form.  Elementary real inequalities then prove `qw(g) ≥ 0`; no positivity
conclusion is stored in the structure.  The corresponding aggregate-profile
and pinned-detector `SourceRH` consumers are now formalized.

This is an interface reduction, not the missing analytic estimate: a future
producer must still construct the same-owner residual identity and prove the
tail bound.  Focused bridge/exit/audit build: 3779 jobs, no `error:` or
`sorryAx`, standard three axioms only.
