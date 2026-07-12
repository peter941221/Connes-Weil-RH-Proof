# 068 M3A Diagonal Regular-Part Verdict

Date: 2026-07-12

Result: the easiest analytic rejection test does not kill M3A. After the
`-2 Dirac` principal term is removed, the CC20 regular remainder has a finite
one-sided diagonal limit. No `1/|rho-1|` or stronger non-`L2` singularity
survives this test.

## Source Formula

For `rho >= 1`, CC20 gives

```text
delta(rho) = 2 sqrt(rho) *
  (Si(2 pi (1+rho))/(2 pi (1+rho))
   + Si(2 pi (rho-1))/(2 pi (rho-1))).
```

It also gives `delta(rho^-1)=delta(rho)`. The right derivative at `rho=1` is
`+1`, while the reflected left derivative is `-1`. Therefore

```text
Q delta = -(rho d_rho)^2 delta + delta/4
        = -2 Dirac_(rho=1) + q_reg.
```

## Local Expansion

Put `h=rho-1`. Expanding the explicit Sine-Integral formula from the right
gives

```text
delta(1+h)
  = 2 + Si(4 pi)/(2 pi)
    + h
    + (-4 pi^2/9 - Si(4 pi)/(16 pi)) h^2
    + O(h^3).
```

Applying `Q` to the regular side yields

```text
q_reg(1+h)
  = 8 pi^2/9 + Si(4 pi)/(4 pi) - 1/2
    + (4 pi^2 - 1) h
    + O(h^2).
```

Hence

```text
lim_(rho -> 1+) q_reg(rho)
  = 8 pi^2/9 + Si(4 pi)/(4 pi) - 1/2
  approximately 8.39172410732812143.
```

High-precision differentiation at distances `10^-2` through `10^-12` from
the diagonal converged to the same value. The numerical check is only a guard;
the Taylor expansion supplies the analytic reason.

## Consequence

On any compact ratio interval `[1,R]`, the explicit regular side is analytic
away from `1` and has the finite limit above at `1`. It is therefore bounded
after continuous extension. On a compact `sqrt(I) × sqrt(I)` rectangle with
logarithmic measure, boundedness is sufficient for square integrability.

This passes only the local regularity test. It does not yet prove:

```text
the exact regularized source formula used by Lean
the kernel-action identity on L2(sqrt(I),d rho)
agreement with the M0-normalized remainder
the selected-test-to-xi same-object bridge
```

## Decision

```text
literal Q-delta kernel: rejected by guard 067
regular k_I diagonal L2 obstruction: not found
next cheapest rejection gate: kernel-action and same-object normalization
M3A status: pending
```
