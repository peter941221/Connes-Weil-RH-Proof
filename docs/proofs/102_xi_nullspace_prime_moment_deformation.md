# 102 Xi-Nullspace Prime-Moment Deformation

Date: 2026-07-12

## New mechanism

Let `H_rho` be the canonical Xi-orbit quotient detector. Instead of forcing a
small physical correction, deform it by

```text
R(s) = s * (s - 1/2) * (s - 1)
H_new(s) = H_rho(s) + completedRiemannXi(s) * R(s) * A(s).
```

At every source zero `z`, the correction vanishes because `Xi(z)=0`. The factor
`R` also preserves the three route zeros. Hence the entire source-zero value
pattern and route vanishings are unchanged:

```text
H_new(z) = H_rho(z).
```

This preserves the negative removed-orbit pairing and every exact non-target
zero before cutoff.

## Why it may alter prime terms

Prime-log autocorrelations are Fourier coefficients of the critical-line
density `|H|^2`. Replacing `H_rho` by `H_new` changes that density through

```text
2 Re(conj(H_rho) Xi R A) + |Xi R A|^2.
```

Thus Xi-null directions are invisible to the spectral zero sum but visible to
prime translations. They may supply the missing degrees of freedom for

```text
autocorrelation(log(p^k)) = 0
```

or, more weakly, for a favorable total finite-prime sign.

## Physical tail

The inverse of `Xi R A` is a finite constant-coefficient differential operator
applied to the convolution of the centered Xi kernel with the inverse transform
of `A`. The Xi kernel has the superexponential two-sided tail recorded in proofs
075 and 081. Compact/superexponential choices of `A` should retain the same
cutoff-summability class.

## Rejection-first gates

1. For a finite set of prime logs, the derivative moment rows
   `A -> Re <Xi A, T_a H_rho>` may fail to be independent.
2. Solving the nonlinear autocorrelation equations may force `A` outside the
   common QW/CC20 form domain.
3. As the cutoff grows, the required family `A_R` may develop unbounded tail
   constants, recreating the radius/count cycle.
4. A single entire `A` nulling every prime-power moment may be an RH-level or
   impossible phase-retrieval problem.

## Status

```text
zero-value preservation: exact algebraic pass
ability to move prime moments: plausible
finite moment surjectivity: open
uniform cutoff control: open
```
