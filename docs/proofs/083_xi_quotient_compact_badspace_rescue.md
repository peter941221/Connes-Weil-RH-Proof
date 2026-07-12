# 083 Xi Quotient Plus Compact Bad-Space Rescue

Date: 2026-07-12

## Correction to proof 082

Proof 082 correctly observed that the Xi quotient does not prove global Weil
positivity by itself. It was too strong to conclude that the quotient therefore
has no lower consumer. The quotient can be consumed by the existing finite-
codimension CC20/M4 sign mechanism on the *same* test.

## Proposed chain

```text
off-critical source zero
  -> canonical Xi quotient and compact cutoff
  -> QW(test) < 0
  -> impose finitely many bad-space orthogonality constraints
  -> test lies in B_I^perp
  -> <test,(-2 Id + K_I) test> < 0
  -> source trace bridge gives QW(test) >= 0
  -> contradiction
```

Here `I` is one fixed bounded cutoff interval. The compactness theorem is used
after `I` is fixed, so its finite-dimensional control space is finite before the
orthogonality constraints are imposed. This is different from asserting a
uniform bound on all growing-cutoff bad spaces.

## Why this may bypass the old cycle

The old M5B construction had to learn all other zeros by finite interpolation,
which created the circular condition `R >= (n_R+1)T_R`. The Xi quotient already
vanishes at every non-target zero. Cutting it off creates one physical tail;
orthogonalizing against `B_I` adds only finitely many linear constraints for the
chosen `I` and does not introduce a new zero radius.

For a fixed `I`, the needed algebraic statement is finite-dimensional: the four
orbit evaluation functionals together with the `B_I` rows must be independent on
the smooth compactly supported test space. The translation-family argument in
proof 080 is evidence for this independence before cutoff. The unresolved part
is quantitative/smooth realization after cutoff, not a global zero-count cycle.

## Cheap death gates

1. The bad-space constraints may annihilate the negative orbit functional. Then
   the joint evaluation matrix is singular and this rescue dies.
2. Orthogonalization may leave the source test algebra or destroy the three
   exact Mellin zeros. The correction must be performed inside the common smooth
   compact test space, not in an ambient `L2` space only.
3. The CC20 sign bridge must apply to the resulting same square and the same
   cutoff. A separately projected vector is not accepted.
4. The compactness threshold can be chosen as `1`: applying
   `exists_finiteDimensional_remainder_nonpositive` to `K_I` gives
   `K_I-I <= 0` on the complement, hence
   `K_I-2I <= -I` there. Compactness alone still gives no uniform threshold
   across changing intervals, so the interval must remain fixed during this
   argument.

## Status

```text
Xi orbit quotient: survives conceptually
single-tail cutoff: survives at reduction level
finite bad-space orthogonalization: new active gate
same-object smooth source bridge: open
Lean owner: still forbidden
```

This is a research route, not an accepted theorem. The next test is a finite
matrix/functional separation calculation on one fixed cutoff interval, followed
by a proof that the finite constraints preserve the source test algebra.
