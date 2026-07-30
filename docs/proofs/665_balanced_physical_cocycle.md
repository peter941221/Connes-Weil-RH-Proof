# Proof 665: balanced physical cocycle

## Result

This proof is a strict normal-form improvement but does **not** close Bone
1A. It removes Proof 664's abstract target projection response from the
active norm and replaces it by one explicit source-side physical cocycle.

Let

```text
K_S = unpolarized restricted Euler frame,
G_S = K_S^dagger K_S,
R_S = G_S^(-1/2),
L_S = R_S G_S,
A_S = K_S^dagger W K_S,
B_0 = J^dagger W J.
```

The two Gram orientations are

```text
Q_S              = A_S G_S^(-1) - B_0,
TargetBoundary_S = B_0 - G_S^(-1) A_S = -Q_S^dagger.
```

Lean also identifies the raw response with the literal three-branch
physical first jet:

```text
Raw_S = FirstJetPhysical_S + Q_S.
```

These identities are important because the target and metric terms cancel
only after they are put on the same suffix.

## Single-suffix cancellation

Define

```text
Z_S
  = FirstJetPhysical_S L_S
    + (A_S R_S - R_S A_S)
    + (L_S B_0 - B_0 L_S).
```

Using

```text
R_S^2 = G_S^(-1),
R_S L_S = I,
G_S^(-1) L_S = R_S,
```

Lean proves

```text
TargetBoundary_S + R_S Raw_S L_S = R_S Z_S.
```

The cancellation flow is therefore

```text
+----------------------+      +----------------------+
| target left Gram     |      | raw right Gram       |
| B_0 - G^-1 A         |      | R(A G^-1-B_0)L       |
+----------+-----------+      +-----------+----------+
           |                              |
           +--------------+---------------+
                          v
             R([A,R] + [L,B_0])
                          +
             R FirstJetPhysical L
                          |
                          v
                       R Z_S
```

Here `[A,R] = A R-R A` and `[L,B_0] = L B_0-B_0 L` are commutators
(commutators). Neither is estimated separately.

## Adjacent route normal form

Proof 664's completed ledger becomes

```text
X_S - X_(p::S)
  = R_(p::S) Z_(p::S) - R_S Z_S.
```

Let `U_(p::S)` be the polar frame and `T_(p,S)` the actual compressed
forward transition. The two exact frame identities are

```text
K_(p::S) R_(p::S) = U_(p::S),

K_(p::S) R_S
  = (1+q_p) U_(p::S) T_(p,S).
```

Consequently the complete ambient column is

```text
K_(p::S)(X_S-X_(p::S))R_S
  = U_(p::S)
      [Z_(p::S)-(1+q_p)T_(p,S)Z_S]R_S.
```

Since `U_(p::S)` is isometric, Lean removes it from the operator norm with
no loss of constants. Bone 1A is therefore equivalent to the existence of a
uniform bound for

```text
q_p^(-1/2)
  [Z_(p::S)-(1+q_p)T_(p,S)Z_S]R_S.
```

The theorem
`exists_routeUniformScaledCompleteTargetBound_iff_physicalCocycle` packages
this equivalence with exactly the same bound.

## Active bottom

The next producer must prove the suffix-uniform estimate

```text
sup_(route-valid p,S)
  q_p^(-1/2)
  ||[Z_(p::S)-(1+q_p)T_(p,S)Z_S]R_S|| < infinity.
```

The correct next decomposition is the adjacent recurrence of the complete
`Z` cocycle. It is not valid to bound the physical first jet and the two
gauge commutators separately: their signed cancellation is precisely what
removed the potentially conditioned target/raw terms.

Proof 656's two-step factor remains a separate Bone 1 requirement. Gate 3U,
the finite-S sign, Burnol's identity, and RH also remain open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPhysicalCocycle.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPhysicalCocycleAudit.lean
```

## Verification

The Windows truth source was copied to the Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 665 focused source             |  3452 | PASS   |
| Proof 665 focused axiom audit        |  3453 | PASS   |
| CCM25Concrete aggregate              |  3940 | PASS   |
| full repository                      |  4021 | PASS   |
+--------------------------------------+-------+--------+
```

All seventeen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
or new source linter warning was added.
