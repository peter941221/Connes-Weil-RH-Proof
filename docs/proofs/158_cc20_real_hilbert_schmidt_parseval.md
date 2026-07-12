# CC20 Real Hilbert--Schmidt Parseval Identity

Date: 2026-07-12

## Result

The compact regular-kernel operator now satisfies the exact Hilbert--Schmidt
Parseval identity for every countably indexed real Hilbert basis:

```text
sum_i ||T(e_i)||^2 = integral_(X x X) ||K(x,y)||^2.
```

Without a countability assumption, the left-hand `tsum` is still proved no
larger than the same product-kernel energy.

## Proof

The full-`L2` coefficient representation identifies `T(e_i)` with the
continuous function `x |-> inner e_i K_x`. Pointwise Hilbert-basis Parseval
gives

```text
sum_i |inner e_i K_x|^2 = ||K_x||^2.
```

The previously proved Hilbert--Schmidt summability supplies the summable
integral norms required by Mathlib's dominated-convergence interchange. The
section norm identity and Fubini then identify the resulting iterated integral
with the squared norm of the same kernel on the product measure.

## Boundary

This closes the real Hilbert--Schmidt Parseval layer. It does not yet provide a
complex-linear same-kernel operator for `PositiveTrace.BasisHilbertSchmidtData`,
identify this ordinary regular kernel with CC20's source `K_I`, establish the
Dirac split or trace read-off, or prove RH.
