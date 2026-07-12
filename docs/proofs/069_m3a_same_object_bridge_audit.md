# 069 M3A Same-Object Bridge Audit

Date: 2026-07-12

Result: no mathematical counterexample was found at the same-object boundary,
but the required bridge is not present in the repository. M3A remains pending;
any implementation that silently identifies these objects is invalid.

## Required Identity

The M3A route needs one selected test `g`, one source transform `F_g`, and one
CC20 convolution root `xi` satisfying

```text
F_g = Q(xi * xi*)
D_infinity(F_g) = <xi, (-2 Id + K_I) xi>
```

The first equality identifies the CCM25 selected square with the CC20 `Q`
image. The second identifies the M0 operator-defined remainder with the CC20
archimedean quadratic form. Both equalities must use the same support interval,
logarithmic measure, cutoff normalization, and involution.

## Repository Boundary

The current owners provide separate pieces:

```text
SelectedWeilSquareOwner
  sourceTest g
  convolutionSquare g*g
  support bound

M0 corrected trace identity
  operator-defined D_(S,Lambda_op)(F_g)
  theta_S(F_g), T_S, P, P_hat

CC20 source theorem
  xi in L2(sqrt(I), d rho)
  D_infinity o Q(xi*xi*)
  -2 Id + K_I
```

No current Lean declaration constructs `xi` from the selected `g`, proves the
`Q`-image identity, or transports the M0 remainder to the CC20 quadratic form.
The existing `HEq`/same-symbol bridges only identify route records; they do not
transport this dependent analytic object and its measure.

## Death-Test Result

The boundary is not itself a contradiction: the source support conventions
could still permit `xi := g` after a correct multiplicative/logarithmic change
of variables. But the identification is not definitional, and the required
operator identity cannot be obtained from support equality alone.

```text
same-object bridge exists in Lean:        no
source mathematics rules it out:          no
safe route status:                         pending
forbidden shortcut:                       rfl, broad simp, HEq by symbols
```

## Next Gate

Construct the bridge on a concrete common test space and prove the two
equalities above before defining `FixedSRemainderData`. If the Mellin half-
density, involution, or `Q` normalization differs, reject M3A at that point
instead of adding a compatibility field that stores the desired conclusion.
