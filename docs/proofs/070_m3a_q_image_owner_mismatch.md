# 070 M3A Q-Image Owner Mismatch

Date: 2026-07-12

Result: the current selected-square owner cannot be used directly as the CC20
M3A `Q`-image. This kills the naive same-object bridge before any kernel-action
proof.

## Definitions In The Repository

`SelectedWeilSquareOwner` stores exactly:

```text
sourceTest : g
convolutionSquare := g* * g
support bound for g* * g
```

The defining equation is in
`ConnesWeilRH/Source/CCM25Concrete/SelectedWeilSquare.lean`:

```text
owner.convolutionSquare.test x
  = integral t, star (g.test (-t)) * g.test (x-t)
```

There is no `Q` operator or Q-root test in this owner.

## CC20 Requirement

The archimedean theorem used by M3A is:

```text
D_infinity o Q(xi * xi*)
  = <xi, (-2 Id + K_I) xi>.
```

Therefore the M0 input must satisfy

```text
F_g = Q(xi * xi*)
```

not merely

```text
F_g = xi * xi*.
```

The support equality is insufficient: `Q` changes the Mellin multiplier and
the test values even though it preserves compact support.

## Why The Naive Bridge Is Invalid

The current owner has no field or theorem providing any of:

```text
xi := sourceTest
Q(sourceTest * sourceTest*) = convolutionSquare
sourceTest = (Q-root of xi)
Mellin multiplier (t^2 + 1/4)
```

Consequently, identifying `F_g` with `Q(xi*xi*)` by `rfl`, `simp`, support
equality, or an `HEq` over route symbols would change the mathematical object.

## Decision

```text
current raw-square -> CC20-Q-image bridge: rejected
corrected Q-root owner: not yet constructed
M3A overall: pending, but naive implementation is dead
```

The only valid reopening is a new data-bearing owner whose source test is a
genuine Q-root (for example, the logarithmic differential multiplier whose
convolution square has Mellin factor `t^2 + 1/4`). That owner must preserve
compact support, smoothness, the selected finite-node constraints, and the M0
normalization on the same object.
