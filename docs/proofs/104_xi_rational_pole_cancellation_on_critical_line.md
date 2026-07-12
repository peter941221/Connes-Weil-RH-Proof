# 104 Xi Rational-Pole Cancellation on the Critical Line

Date: 2026-07-12

## Algebraic reduction

Write the canonical detector in the form

```text
H_0(s) = Xi(s) * R(s) * S(s) / P_rho(s),
R(s)=s(s-1/2)(s-1),
```

where `P_rho` removes the finite off-critical symmetry orbit and `S` assigns
the desired orbit values. The formal Xi-null correction that cancels `H_0` is

```text
A_*(s) = -S(s)/P_rho(s).
```

`A_*` is not entire because its poles are exactly the removed orbit. That
failure is useful: it preserves the nonzero detector values at those poles.

## Critical-line approximation

If the marked zero is off the critical line, the poles of `A_*` have positive
distance

```text
delta = |Re(rho)-1/2| > 0
```

from the centered critical line. Hence the restriction of `A_*` to that line
is analytic in a strip of width `delta`; its inverse Fourier transform decays
exponentially. Truncating that inverse transform at radius `T` gives an entire
function `A_T` of finite exponential type with convergence

```text
A_T -> A_*
```

in every fixed polynomially weighted Sobolev norm on the critical line.

Define

```text
H_T = H_0 + Xi * R * A_T
    = Xi * R * (S/P_rho + A_T).
```

At every zeta zero, the correction is exactly zero; at the removed orbit,
`H_T` retains the quotient's finite nonzero limiting values. On the critical
line, `H_T` tends to zero in strong weighted norms.

## Why this improves Plan 030

Small weighted critical-line norm controls all bounded translation
autocorrelations simultaneously. It does not solve one prime moment at a time,
so the number of visible prime powers need not enter the approximation
dimension. Finite M4 orthogonality rows can be added to the Paley--Wiener
approximation as finitely many linear constraints.

## Rejection-first gates

1. Prove the exact strip/Fourier decay of `S/P_rho`, including multiplicities
   and conjugate orbit collisions.
2. Show multiplication by `Xi*R` maps the weighted approximation error into
   the common QW/CC20 form topology.
3. Prove the explicit-formula/finite-prime functional is continuous in that
   topology; `L2` alone is insufficient.
4. Perform the final physical cutoff without losing the fixed negative orbit
   margin or recreating a support/count cycle.

## Status

```text
exact preservation of all zero values: pass
linear critical-line cancellation mechanism: pass conceptually
Paley-Wiener weighted approximation: standard but unproved locally
full QW form-topology continuity: open and decisive
```

