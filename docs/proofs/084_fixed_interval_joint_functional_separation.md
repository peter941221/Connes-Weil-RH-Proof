# 084 Fixed-Interval Joint Functional Separation

Date: 2026-07-12

## Purpose

This is the smallest mathematical gate for the rescue in proof 083. It avoids
any uniform condition-number claim across growing cutoffs. Choose one bounded
log interval `I` first, then work on the vector space
`C_c^infinity(interior I)`.

## Functionals

For a fixed `I`, collect the following finite family:

```text
L_1,...,L_3       triple Mellin zero constraints
E_1,...,E_4       values on the removed Xi orbit
B_1,...,B_m       inner products with a basis of the M4 bad space B_I
```

The desired statement is that this family is linearly independent. Finite
independence then implies surjectivity onto `C^(3+4+m)`: if the image were a
proper subspace, a nonzero linear functional on the target would vanish on the
image, contradicting independence. A finite linear combination of compact
smooth witnesses gives one common support interval and solves all constraints
exactly.

## Why independence is plausible

The Mellin and orbit rows are exponential functions of a real translation
parameter. A bad-space row is a convolution of the quotient inverse with a
compactly supported bad vector, so it decays at both translation tails. If a
linear combination of all rows vanished on an open translation interval,
analytic continuation and the two tails first kill the exponential rows. The
remaining convolution identity has Fourier transform

```text
Q_hat * (sum_j beta_j e_hat_j) = 0.
```

The Xi quotient is nonzero, so the identity theorem forces the bad-vector
combination to vanish. This is the argument already isolated in proof 080 and
is the same linear-dual mechanism used by the repository's finite-window
Mellin theorem (`CC20YoshidaConstruction.lean`,
`positive_interval_expanded_mellin_surjective_of_linear_dual_separation`).

## Exact failure modes

The argument does **not** yet prove the route gate. It fails if any of the
following source-facing identifications fail:

1. The four orbit values are not continuous linear functionals of the chosen
   compact test after the centered half-density and Q-root are included.
2. The M4 bad vectors do not pull back to compactly supported continuous rows on
   the same test space.
3. A nonzero quotient transform has an interval of zeros, invalidating the
   Fourier identity argument.
4. The source test algebra is a proper subspace of the smooth compact space and
   does not contain the finite witness combinations.

The first three are analytic ownership obligations; the fourth is the likely
cheap project-specific death gate.

## Decision

```text
abstract finite joint separation: passes
repository interpolation pattern: available
same centered source owner: open
source-algebra closure under finite witnesses: open and next target
```

No Lean owner should be added until the four functionals are defined on one
same source test object and the closure statement is proved.

