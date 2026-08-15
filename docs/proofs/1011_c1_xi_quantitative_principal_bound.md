# 1011 Quantitative Xi Finite Principal-Part Bound

Date: 2026-08-14

## Result

`C1XiQuantitativePrincipalBound` closes the quantitative estimate for the
finite pole part of the xi logarithmic derivative on the same dyadic,
two-sided zero-free heights chosen by `C1XiQuantitativeHeight`.

For every `n`, the endpoint

```lean
exists_dyadic_quantitative_xiHeight_tubes_principal_bound
```

selects one height `T_n` with

```text
2^(n + 2) < T_n < 2^(n + 2) + 1
```

and returns both zero-free tubes together with

```text
|| P_n(x + T_n*i) || <= 4 * N_n * (N_n + 2)
|| P_n(x - T_n*i) || <= 4 * N_n * (N_n + 2)

N_n = spectralMultiplicityConstant * 3^(n + 1).
```

Here `P_n` is the exact finite principal sum from the origin-centered
closed-ball xi factor owner of radius `T_n + 2`:

```text
P_n(z) = sum_(u in divisor support)
           multiplicity(u) / (z - u).
```

This is an `O(9^n)` bound for the finite principal part. It does not bound the
zero-free cofactor term in the same factorization, so it is not a full
`xi'/xi` bound.

## Why It Holds

The proof uses one owner throughout.

```text
same closed-ball xi divisor owner
        |
        +-- each support point is a genuine xi zero
        |
        +-- same-owner reindex to source zeros
        v
mass(P_n) <= finiteHeightMultiplicity(T_n + 2)
        |
        +-- T_n + 2 <= 2^(n + 3)
        +-- dyadic Jensen estimate
        v
mass(P_n) <= N_n
        |
        +-- zero-free tube excludes every xi zero from radius r_n
        v
dist(x +/- T_n*i, u) >= r_n for every divisor point u
        |
        v
||P_n|| <= mass(P_n) / r_n
```

The dyadic tube radius has no active half-unit cap at these scales:

```text
r_n = 1 / (4 * (N_n + 2)).
```

Substitution gives the closed estimate:

```text
mass(P_n) / r_n
  <= N_n / (1 / (4 * (N_n + 2)))
   = 4 * N_n * (N_n + 2).
```

The critical separation is mathematical, not only type-level. The finite
factor support is a set of xi zeros, and the selected tube is zero-free for
all complex points on both horizontal lines. A support point closer than
`r_n` would therefore be a forbidden zero inside that tube.

## Public Interface

The module exposes the intermediate ownership-preserving facts:

```lean
norm_xiClosedBall_principalSum_le_divisorMass_div
xiClosedBallDivisorMass_zero_eq_sourceMultiplicitySum
xiClosedBallDivisorMass_zero_le_finiteHeightMultiplicity
norm_xiClosedBallPrincipalSum_zero_le_finiteHeightMultiplicity_div_of_tube
finiteHeightMultiplicity_selected_dyadic_le
```

They separate the three ingredients needed by a later analytic cofactor
argument: finite pole geometry, source multiplicity counting, and the
remaining zero-free analytic factor.

## Remaining Root

```text
dyadic Jensen zero count                     CLOSED
same-height two-sided zero-free tubes        CLOSED
finite xi principal-part O(9^n) bound        CLOSED
zero-free cofactor minimum-modulus bound     OPEN
quantitative cofactor log-derivative bound   OPEN
full xi'/xi horizontal bound                 OPEN
horizontal contour limit                     OPEN
```

A zero-free tube alone cannot close the remaining cofactor line: a nonzero
holomorphic function can have arbitrarily small modulus. The next theorem
needs a quantitative lower bound for the cofactor, or an equivalent
normalized analytic-log argument that supplies one.

## Verification

The isolated WSL2 ext4 verification ran:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiQuantitativePrincipalBoundProbe
```

It completed all 3536 jobs. The eight audited declarations depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurred.
