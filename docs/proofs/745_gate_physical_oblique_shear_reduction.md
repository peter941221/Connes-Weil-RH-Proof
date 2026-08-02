# Proof 745: Gate Physical Oblique-Shear Reduction

## Result

The result is structurally useful but does not close Gate 3U.  Proof 745
shows that Proof 744's pulled projection differs from the source Sonin
projection by one square-zero source/complement crossing.

Write

```text
R   = sourceSoninProjection,
Q_S = T_S^(-1) P_S T_S,
N_S = Q_S-R.
```

The actual target Gram formula gives

```text
Q_S
  = (J G_S^(-1) J^dagger)(T_S^dagger T_S).            (OS.1)
```

The first factor in `(OS.1)` lands in the source Sonin range.  Lean therefore
proves the missing range identity

```text
R Q_S = Q_S.                                           (OS.2)
```

Together with Proof 744's `Q_S R=R`, this completely determines the block
shape of `Q_S` relative to `R H + (I-R)H`:

```text
            source R     complement I-R
          +------------+----------------+
source R  |     I      |       B_S      |
          +------------+----------------+
comp I-R  |     0      |        0       |
          +------------+----------------+

Q_S = [ I  B_S ],       N_S = Q_S-R = [ 0  B_S ].
      [ 0   0  ]                         [ 0   0  ]
```

Here `B_S` is not assigned a separate norm bound.

## Square-Zero Structure

Lean proves all four exact block identities

```text
R N_S = N_S,
N_S R = 0,
N_S^2 = 0,
N_S = R Q_S (I-R).                                    (OS.3)
```

Thus all finite-family dependence that survives in the target response is a
one-way oblique shear from the source complement into the source Sonin range.

## Gate Reduction

Proof 744 gave

```text
Target_S = J^dagger (Q_S-I) W J.
```

Because `J^dagger R=J^dagger`, replacing `I` by `R` after the left readback
is exact.  Lean obtains

```text
Target_S = J^dagger N_S W J.                          (OS.4)
```

The same operator is Proof 744's fixed-source commutator owner:

```text
J^dagger Q_S[W,R]J = J^dagger N_S WJ.                 (OS.5)
```

Consequently the route-facing quantifiers reduce to

```text
(exists C, forall S, |Tr(Gate_S)| <= C)
  <->
(exists C, forall S, |Tr(J^dagger N_S W J)| <= C).    (OS.6)
```

No trace cycle is used in `(OS.4)`--`(OS.6)`.

## Nilpotence Guard

`N_S^2=0` does not make the response in `(OS.4)` vanish.  A two-dimensional
model already shows the failure:

```text
R = [1 0],   N = [0 b],   W = [0 1],   Jx = [x].
    [0 0]        [0 0]        [1 0]        [0]

J^dagger N W J = b.
```

The detector first crosses from the source range to its complement; the
shear then returns that component to the source range.  Nilpotence only says
that two consecutive shear steps vanish.

Do not estimate `N_S`, `B_S`, or the lifted inverse Gram separately.  Such an
estimate can recover the Euler condition number.  The remaining producer
must use compact-root support in the complete signed trace of `(OS.4)` before
taking an absolute value.

## Verification

The Windows source of truth was copied one way to the Ubuntu-24.04 WSL2 ext4
verification tree.  The accepted builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3389 | PASS   |
| CCM25Concrete aggregate          |  4013 | PASS   |
| full repository                  |  4094 | PASS   |
+----------------------------------+-------+--------+
```

All ten audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source and audit contain
no `sorry`, `admit`, user axiom, heartbeat increase, recursion-limit
increase, unsafe declaration, new linter warning, or line over 100
characters.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
