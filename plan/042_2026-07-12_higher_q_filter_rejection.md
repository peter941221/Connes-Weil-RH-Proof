# 042 Higher-Q Filter Rejection

Date: 2026-07-12

Status: rejected as a way to amplify the archimedean negative scalar.

## Source Fact

CC20's `Q=-(rho partial_rho)^2+1/4` is the minimal support-preserving operator
whose Mellin multiplier vanishes at the two pole nodes.  In log coordinates,
the archimedean defect has one derivative cusp:

```text
delta(exp(|x|)) = smooth_even(x) + |x|,
Q delta(exp(|x|)) = -2 delta_0 + smooth_function.
```

This is why the root-space operator is `-2 Id+K_I`.

## Candidate

Replace `Q` by a higher support-preserving polynomial filter

```text
P(D)=Q(D) R(D),
```

where `R` preserves the route zeros and is nonnegative on the real Mellin line,
hoping to obtain a larger negative scalar and absorb finite-prime costs.

## Death Gate

Applying `R(D)` to the cusp produces derivatives of the Dirac distribution:

```text
delta', delta'', ...
```

On a convolution root these become derivative energies such as
`<D^j xi,D^k xi>`.  Their Fourier symbols grow polynomially in the frequency,
so the resulting root operator is unbounded and not `-c Id+compact`.

If `R` is a scalar, it scales the archimedean and prime terms together and gives
no relative compensation.  If `R` has positive degree, the unbounded derivative
channels cannot be removed by finite-dimensional M4 conditioning.

## Verdict

```text
Q minimal cusp-to-Dirac filter: source-backed
scalar rescaling: no relative gain
higher differential filter: unbounded derivative remainder
Plan 042: rejected
```

See proof 120 and CC20 `weil-compo.tex:186-196, 712-750, 765-808`.

