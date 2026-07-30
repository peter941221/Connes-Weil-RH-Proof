# Proof 635: ambient covariance factor

## Result

Proof 635 rewrites the complete signed numerator as the pullback of one
ambient covariance column.  Let

```text
U_S = actual suffix polar frame,
Q_S = complete raw quadratic response,
Z_S = U_S Q_S U_S^dagger,
F_p = normalized forward Euler transport.
```

Define the intact covariance column

```text
C_(p,S) = (F_p Z_S - Z_(p::S) F_p) U_S.
```

Lean proves

```text
C_(p,S) = U_(p::S) rawIntertwiningDefect_(p,S),

K_(p,S)^dagger T_(p,S)
  = U_S^dagger N_p C_(p,S).
```

The first jet, endpoint Gram correction, outer and reflected boundaries,
second support, and prolate term remain recombined inside `Q_S`.

## Exact Bone 1 producer

A route-uniform factorization

```text
C_(p,S) = L_p H_(p,S),
sup_(route-valid p,S) ||H_(p,S)|| < infinity
```

immediately gives

```text
K_(p,S)^dagger T_(p,S)
  = U_S^dagger N_p L_p H_(p,S),
```

which is exactly Proof 627's single-channel producer.  Lean packages the
fixed-step and route-uniform covariance factors and maps them directly to the
existing Bone 1 domination contract without norm loss.

```text
 complete adjacent response Q_S
              |
              v  lift through actual polar frames
 ambient covariance C_(p,S)
              |
              v  missing source theorem: C = L H, ||H|| uniform
 renewed single-channel factor
              |
              v  Proofs 627-628
 Bone 1
```

## Boundary

Proof 635 identifies a concrete sufficient producer; it does not construct
`H`.  Proof 637 shows that this target is stronger than Bone 1 by an explicit
moving-range leakage.  It remains useful because it lives on the actual
global-log carrier and preserves the complete covariance before any absolute
value.  Compactness from Proof 631, the empty-suffix bound from Proof 632, and
radial recovery from Proofs 633-634 do not by themselves control the
second-support/prolate covariance rate.

Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorAmbientCovariance.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorAmbientCovarianceAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| ambient-covariance source            |  3400 | PASS   |
| focused seven-declaration audit      |     - | PASS   |
| CCM25Concrete aggregate              |  3909 | PASS   |
| full repository                      |  3990 | PASS   |
+--------------------------------------+-------+--------+
```

All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
