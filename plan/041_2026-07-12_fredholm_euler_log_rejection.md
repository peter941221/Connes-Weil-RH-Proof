# 041 Fredholm Euler-Log Rejection

Date: 2026-07-12

Status: rejected before empirical or Lean work.

## Candidate

Use a Fredholm or bosonic-Fock determinant to generate

```text
-log det(I-aU_p)
  =sum_(m>=1)a^m Tr(U_p^m)/m,
```

then let the crossing length supply `m log(p)`.

## Death Gates

1. `U_p` is a unitary translation on an infinite-dimensional `L2` space.  It
   is not compact or trace class, so `det(I-aU_p)` is not a Fredholm
   determinant.
2. The cross-half-line block is a partial translation between intervals of
   length `log(p)`.  It has infinitely many singular values equal to one and is
   also not compact.
3. Test smoothing can turn a boundary block into a Hilbert--Schmidt operator,
   but the regularized determinant `det_2` removes the linear `m=1` trace.
4. Powers of the smoothed block are powers of the test-dependent operator, not
   the raw translations `U_p^m`; their traces do not read the same convolution
   square at `m log(p)`.

## Verdict

```text
formal Euler logarithm coefficients: correct
Fredholm determinant of raw owner: undefined
bosonic Fock partition trace: divergent
det_2 repair: loses m=1 and same-object read-off
Plan 041: rejected
```

See proof 119.

