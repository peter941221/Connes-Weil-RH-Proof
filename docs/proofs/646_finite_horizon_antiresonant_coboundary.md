# Proof 646: finite-horizon antiresonant coboundary

## Result

Proof 646 constructs an explicit finite-horizon readout.  It is not another
existential Douglas contract.

For

```text
L = s (I + U),
P_N(U) = sum_(0 <= k < N) (-U)^k,
H_N = s^(-1) C P_N(U),
```

Lean proves the exact telescope

```text
P_N(U)(I + U) = I - (-U)^N,
H_N L = C - C(-U)^N.
```

Thus one terminal orbit term is the whole obstruction.  If
`C(-U)^N = 0`, the displayed `H_N` is an exact factor through `L`.

For `||U|| <= 1` and `s != 0`, the explicit norm bound is

```text
||H_N|| <= N ||C|| / ||s||.
```

No block-count or hidden infinite inverse occurs.

## Actual orientation

The sign and translation direction are now explicit:

```text
primeEulerAmbientLossFactor(p)
  = s_p (I + U_(-log p)),

primeEulerAmbientLossFactor(p)^dagger
  = s_p (I + U_(+log p)).
```

The raw Bone 1 column uses the adjoint and therefore the positive translation.
Proof 646 instantiates `U = U_(+log p)`.

## Complete coupled ambient target

Write `K_(p,S)` for Proof 641's complete swapped local cofactor.  Proof 646
defines the canonical ambient target

```text
C_(p,S)
  = -rho_p^(-1) Transition_(p,S)^dagger
      K_(p,S) newFrame_S^dagger.
```

Because `newFrame_S^dagger newFrame_S = I`, Lean proves

```text
C_(p,S) newFrame_S = signedCompressedInteriorOwner_(p,S).
```

The whole cofactor stays inside `C_(p,S)`.  Its outer, reflected,
second-support, and prolate branches are never separated.

## Actual endpoint formula

The constructed route readout is

```text
H_(p,S,N)
  = s_p^(-1) C_(p,S)
      sum_(0 <= k < N) (-U_(log p))^k.
```

Define the complete terminal tail

```text
Tail_(p,S,N)
  = C_(p,S) (-U_(log p))^N newFrame_S.
```

Lean proves the same-object identity

```text
H_(p,S,N) (L_p^dagger newFrame_S)
  = signedCompressedInteriorOwner_(p,S) - Tail_(p,S,N).
```

Therefore the exact remaining source theorem is

```text
Tail_(p,S,N) = 0
```

for some usable finite horizon.  Under precisely that premise, the explicit
`H_(p,S,N)` factors the full signed owner through the raw Bone 1 column.

## Why compact support does not close the terminal theorem yet

Compact detector support cuts off distant scalar correlations.  Proof 644
shows that this does not by itself make a translated completed crossing
operator zero.  Consequently no current source theorem proves
`Tail_(p,S,N) = 0` on all source vectors.

The construction is still substantive: it replaces an arbitrary unknown
readout by one explicit alternating polynomial and leaves one concrete
coupled-tail identity, rather than a general relative-energy premise.

## Route judgment

```text
+------------------------------------------------------+----------------------+
| layer                                                | status               |
+------------------------------------------------------+----------------------+
| generic alternating telescope                       | proved               |
| explicit finite-horizon readout                      | constructed          |
| horizon/scale norm bound                             | proved               |
| ambient loss translation orientation                 | proved               |
| complete coupled cofactor ambient extension          | proved               |
| exact route endpoint minus one terminal tail         | proved               |
| terminal coupled-tail annihilation                   | open                 |
| route-uniform horizon/readout bound                   | open                 |
| Bone 1 / Gate 3U / finite-S sign / Burnol / RH       | open                 |
+------------------------------------------------------+----------------------+
```

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorFiniteHorizonCoboundary.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorFiniteHorizonCoboundaryAudit.lean
```

## Verification

The Ubuntu-24.04 WSL2 ext4 source/audit build passed under the shared Lake
lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| finite-horizon coboundary source     |  3393 | PASS   |
| focused seventeen-declaration audit  |  3394 | PASS   |
+--------------------------------------+-------+--------+
```

All seventeen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Bone 1 is not proved.
