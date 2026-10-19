# Fourth-order tail gives an explicit far-frequency credit ceiling (record 3057)

Date: 2026-10-19.

Status: paper-level owner-parameterized upper bound on the far positive credit.
It is not a positive-credit supplier, Lean theorem, or RH result.

## Same-owner symbol and tail

Use record 1738's exact joint symbol for one selected owner:

```text
qw(g) = (1/(2*pi))*integral_R m_S(t)*|G(t)|^2 dt,
m_S(t) = A(t) - sum_(p in S) log(p)*P_p(t),
A(t) = -K + 2*sum_(j>=0) t^2/(c_j*(c_j^2+t^2)),
c_j = 2*j + 1/2.
```

Here `G(t)=L_h(1/2+i*t)=laplaceAt g (i*t)` includes the selected base
power and correction transform, so this is the same owner as the tail bound.

For each visible prime `p`, put `r_p=p^(-1/2)` and

```text
P_p(t) = (1-r_p^2)/(1-2*r_p*cos(log(p)*t)+r_p^2)-1,
C_S = 2*sum_(p in S) log(p)*r_p/(1-r_p).
```

The elementary denominator bound gives `|P_p(t)| <= 2*r_p/(1-r_p)`, hence
`|sum log(p)*P_p(t)| <= C_S` for every real `t`.

The fourth-order geometry tail, restricted to `Re(z)=1/2`, gives record
3054's owner-specific pointwise bound

```text
|G(t)| <= 4*epsilon/|t|^2,  |t| >= T_*,
T_* = max(T,1,2*|Im rho|).
```

## Logarithmic growth of the archimedean symbol

For `t >= 1`, split the positive series defining `A(t)+K` at
`c_j=2*j+1/2 <= t`. On that part,

```text
2*t^2/(c_j*(c_j^2+t^2)) <= 2/c_j.
```

The `j=0` term is at most `4`; for `j>=1`, `2/c_j <= 1/j`. The harmonic
sum through `j<=t` is at most `1+log(t)`. For the remaining terms,

```text
2*t^2/(c_j*(c_j^2+t^2)) <= 2*t^2/c_j^3.
```

The spacing `c_(j+1)-c_j=2` gives
`sum_(c_j>t) c_j^(-3) <= t^(-3) + (1/2)*integral_t^infinity x^(-3)dx`.
Thus the remaining contribution is at most `2/t+1/2 <= 5/2`. Since
`-K<0` and `log(t)<=log(1+t)`, a convenient uniform bound is

```text
A(t) <= 8 + log(1+t),  t >= 1.
```

Therefore

```text
m_S(t) <= 8 + C_S + log(1+t),  t >= 1.
```

## Far-tail credit bound

Let `T_S` be any threshold from record 1738 such that `m_S(t)>=0` for
`|t|>=T_S`, and set `U=max(T_*,T_S,1)`. The positive credit beyond `U` is

```text
C_tail(U) = (1/(2*pi))*integral_(|t|>=U) m_S(t)*|G(t)|^2 dt.
```

Using both signs of `t`, the symbol bound, and `log(1+t)<=log(t)+log(2)` for
`t>=1`,

```text
C_tail(U)
  <= (16*epsilon^2)/(3*pi*U^3)
       * (8 + C_S + log(2) + log(U) + 1/3).
```

Indeed,
`integral_U^infinity t^(-4)dt=1/(3U^3)` and
`integral_U^infinity log(t)*t^(-4)dt=(log(U)/3+1/9)/U^3`.

The negative set `N_S={t:m_S(t)<0}` lies inside `[-T_S,T_S]`, so its entire
deficit is in `[-U,U]`. Splitting the positive credit at `U`, the target
`qw(g)>=0` necessarily implies

```text
credit_(|t|<=U) >= deficit - C_tail(U).
```

Here `credit_(|t|<=U)` integrates only over
`{|t|<=U and m_S(t)>=0}`; it excludes the negative band by definition.

This turns the outer tail into an explicit allowance and locates the required
positive contribution in a finite frequency window. It does not prove that
the window contains enough mass. If `deficit-C_tail(U)` is positive, that
finite-window lower bound is the remaining binding estimate. If it is
nonpositive, the bound is simply inconclusive.

## Scope and next step

`C_S`, `T_S`, `T_*`, epsilon, and `G` all belong to the same geometry; none
may be frozen while changing the selected owner or visible-prime set. The
bound is paper-level and uses the exact symbol from record 1738 plus the
critical-line tail consequence of record 3054. It improves the route map by
pricing the far positive credit, but it cannot replace a same-owner lower
bound on the finite-window positive credit.

The next target is therefore a finite-window estimate for

```text
integral_({|t|<=U, m_S(t)>=0) m_S(t)*|G(t)|^2 dt
```

against the actual deficit on the same owner. The finite Laplace pins and
`FourthOrderSpectralTail` must be used together; the interpolation-only
counterfamily of record 3055 does not apply to the full tail-constrained class.

Evidence:

- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md` gives
  the joint symbol, `C_S`, and existence of `T_S`.
- `docs/proofs/3054_fourth_order_tail_to_derivative_energy.md` gives the
  critical-line transform bound from `FourthOrderSpectralTail`.
- `ConnesWeilRH/Dev/C1C3SigmaKernel.lean` supplies the same archimedean
  profile through the `Gamma_R` logarithmic derivative.
