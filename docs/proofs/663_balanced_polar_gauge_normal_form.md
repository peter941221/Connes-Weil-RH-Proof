# Proof 663: balanced polar-gauge normal form

## Result

This proof is useful but does **not** close Bone 1A.  It removes the adjacent
transition skew from the remaining Proof 662 response by an exact change of
source coordinates.

For the suffix Gram `Gamma_S`, define

```text
R_S = Gamma_S^(-1/2),
L_S = R_S Gamma_S,
M_S = RoutePolarKernel_S - FirstJetResponse_S,
X_S = R_S M_S L_S.
```

Lean proves both inverse identities

```text
R_S L_S = I,
L_S R_S = I,
```

and the literal adjacent transition formula

```text
T_(p,S) = (1 + q_p)^(-1) L_(p::S) R_S.
```

Therefore the complete one-sided mismatch from Proofs 660--662 is

```text
T_(p,S) M_S - M_(p::S) T_(p,S)
  = (1 + q_p)^(-1)
      L_(p::S) (X_S - X_(p::S)) R_S.
```

No equality between `T_(p,S)` and its adjoint is used.

## Ambient cancellation

Let `K_(p::S)` be the unpolarized restricted Euler frame.  The old polar
frame satisfies

```text
oldFrame_(p,S) L_(p::S) = K_(p::S).
```

Thus the left gauge disappears when the source defect is lifted to Proof
662's ambient covariance column:

```text
MetricFirstJetResidual_(p,S)
  = (1 + q_p)^(-1)
      K_(p::S) (X_S - X_(p::S)) R_S.
```

Since

```text
s_p = sqrt(q_p) / (1 + q_p),
```

the genuinely scaled residual is exactly

```text
s_p^(-1) MetricFirstJetResidual_(p,S)
  = sqrt(q_p)^(-1)
      K_(p::S) (X_S - X_(p::S)) R_S.
```

Consequently Lean proves, with the same bound and no constant loss,

```text
Bone 1A route-uniform complete-target bound exists
  <->
route-uniform bound of
  sqrt(q_p)^(-1) K_(p::S) (X_S - X_(p::S)) R_S exists.
```

## What remains

The new normal form isolates a square-root modulus-of-continuity problem.  A
successor must control the completed product

```text
K_(p::S) (X_S - X_(p::S)) R_S
```

at order `sqrt(q_p)`, uniformly over route-valid suffixes.  It is not legal to
bound `K_(p::S)`, `R_S`, or the two balanced responses separately: those
factors can be ill-conditioned and the cancellation belongs to the completed
product.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorPolarGaugeNormalForm.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorPolarGaugeNormalFormAudit.lean
```

## Verification

The Windows truth source was copied to an Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 663 focused audit              |  3450 | PASS   |
| CCM25Concrete aggregate              |  3938 | PASS   |
| full repository                      |  4019 | PASS   |
+--------------------------------------+-------+--------+
```

All twelve audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added.
