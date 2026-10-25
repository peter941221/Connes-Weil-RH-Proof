# Route-B fixed lambda=24 gate adapter (3107)

Date: 2026-10-25.

The row-B contradiction contract fixes the span coefficient at `lambda = 24`.
The earlier four-point algebra only proves an existential statement: under a
diagonal or determinant condition, some positive coefficient may make the
quadratic gate nonpositive. A fixed coefficient requires its own signed
inequality.

This record adds four Lean-checked declarations:

```text
hgate24Predicate3107_iff_gate_qform
  fixed hgate24 expression
    <-> [1, -24] gateMatrix quadratic form <= 0

hgate24Predicate3107_iff_signed_margin
  fixed hgate24 expression
    <-> D + 24^2*C <= 24*cross

hgate24Predicate3107_iff_owner_gate
  package owner hgate24 expression
    <-> same-owner orbitWindowSemiLocalGate at 24

fixed_lambda24_not_implied_by_discriminant3107
  scalar determinant-feasible example with fixed lambda=24 infeasible
```

The third theorem uses the `RhoOwnerPackage3106` owner. Its support radius is
derived from the package geometry, and the annihilator and detector are the
same `g`; no owner substitution is introduced.

The fourth theorem is a formal guard. For the scalar values `D = 1`, `C = 1`
and `cross = 2`, the determinant is zero and the vertex coefficient is
feasible, while the value at 24 is `1 - 24*2 + 24^2 = 529 > 0`. Therefore the
existing “some positive lambda” theorem cannot be used as a proof of row-B's
lambda 24.

Verification was run in the Linux ext4 mirror:

```text
lake build ConnesWeilRH.Dev.C1RouteBFixedLambdaGate3107Audit
```

The build completed successfully with 3830 jobs. The audit output reports no
error lines and no `sorryAx`; all four declarations have exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The signed margin itself remains open. The next mathematical target is an
owner-grade proof of that margin (or a formally certified no-go), followed by
the still-open cardinal pins and shell obligations. This record does not
claim a producer result or the Riemann Hypothesis.
