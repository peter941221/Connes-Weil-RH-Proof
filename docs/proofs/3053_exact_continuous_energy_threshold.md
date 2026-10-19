# Exact continuous energy threshold for the selected Weil functional (record 3053)

Date: 2026-10-19.

Status: paper-level exact decomposition and sharper analytic bound. No new
Lean theorem, numerical owner estimate, signed prime-discrepancy bound, or RH
proof.

## Setup and evidence

Use the same compact-log test `g` and convolution square as record 1736. Define

```text
M       = integral_R |g(x)|^2 dx
E_g(y) = integral_R |g(x+y)-g(x)|^2 dx
f(y)   = Re((g.involution.convolution g).test y)
w(y)   = exp(y/2) / (exp(y)-exp(-y)),                  y > 0
K       = log(8*pi) + EulerGamma + pi/2.
```

Translation invariance gives `f(y) = M - E_g(y)/2`. Record 1736 derives the
continuous part of the exact discrepancy formula as

```text
Q_cont(g) = 2 * integral_0^infinity exp(-y/2) * f(y) dy
            - archimedeanTerm(g.involution.convolution g).
```

The same record gives
`archimedeanTerm = K*M - integral w(y)*E_g(y) dy` and proves
`E_g(y) <= y^2 * D`, where `D = integral_R |g'(x)|^2 dx`.

## Exact decomposition

Substitute `f = M - E_g/2` and use
`integral_0^infinity exp(-y/2) dy = 2`:

```text
Q_cont(g) = (4-K)*M + integral_0^infinity v(y)*E_g(y) dy,
v(y) = w(y) - exp(-y/2)
     = exp(-y/2) / (exp(2*y)-1) > 0.
```

This separates the continuous main term into a negative mass charge and a
positive translation-energy correction. The positivity of the correction is
exact; it does not by itself determine the sign of `Q_cont`.

## Sharper derivative-energy bound

Expand the positive kernel as a geometric series:

```text
v(y) = sum_{k>=1} exp(-(2*k + 1/2)*y).
```

Tonelli's theorem and `integral_0^infinity y^2*exp(-a*y) dy = 2/a^3` give

```text
J = integral_0^infinity y^2*v(y) dy
  = 16 * sum_{k>=0} 1/(4*k+5)^3.
```

For the decreasing function `q(x) = 1/(4*x+5)^3`,

```text
sum_{k>=0} q(k)
  <= q(0) + q(1) + integral_1^infinity q(x) dx
  = 1/125 + 1/729 + 1/648.
```

Hence `J <= 15914/91125 < 1/5`. Using `E_g(y) <= y^2*D` yields

```text
Q_cont(g) <= -(K-4)*M + (1/5)*D.
```

Record 1736 proves `K > 4`, so this sharper estimate implies
`Q_cont(g) < 0` whenever `D/M < 5*(K-4)` and `M > 0`. Compared with the
older coefficient `18`, the new coefficient `1/5` is 90 times smaller.

## Consequence for the prime discrepancy

Under triple vanishing, the exact full identity is

```text
qw(g) = Q_cont(g) + 2*integral_0^infinity R(y)*H_g'(y) dy,
H_g(y) = exp(-y/2)*f(y),
R(y) = Psi(exp(y)) - (exp(y)-1).
```

Therefore the sign target is equivalently

```text
2*integral R(y)*H_g'(y) dy >=
  (K-4)*M - integral v(y)*E_g(y) dy.
```

When `D/M < 5*(K-4)`, the right side is strictly positive by the proved
upper bound on the energy correction. Thus in that parameter regime, any
proof of `qw(g) >= 0` must extract a positive, quantitatively large
contribution from the actual prime discrepancy. Replacing `Psi(exp(y))` by
its continuous main term removes precisely that required contribution.

## Scope and next mathematical test

This is not an owner estimate. The selected correction family constrains
support and finitely many Laplace values, but does not currently give the
required ratio `D/M` or the signed discrepancy integral. In particular,
near-pin derivative-cost obstructions prevent silently assuming a uniform
small value of `D/M`. Record 3054 transfers the existing fourth-order spectral
tail into a Plancherel bound for the high-frequency part of `D`; its low-
frequency remainder is `T_*^2*M`, so that tail field alone still does not
establish the small-ratio condition at large zero height.

The next useful test is to evaluate the two dimensionless owner quantities

```text
r_owner = D/M,
d_owner = (2/M) * integral R(y)*H_g'(y) dy
```

on the actual selected geometry and compare `d_owner` with
`K-4 - (1/M)*integral v*E_g`. Such a calculation is only a routing probe;
it becomes evidence for the proof after an exact owner transfer and certified
quadrature/error bound are supplied. A failed probe must be scoped to the
tested owner and cannot rule out all Route-A geometries.

Sources:

- `docs/proofs/1736_detector_sign_translation_energy_and_prime_discrepancy.md`
  supplies the exact energy identity, the full Stieltjes identity, and `K>4`.
- `docs/proofs/3052_selected_physical_profile_chebyshev_readback.md` identifies
  the same selected owner's smoothed von Mangoldt profile.
- `docs/proofs/3054_fourth_order_tail_to_derivative_energy.md` derives the
  same-owner high-frequency derivative-energy consequence of the existing
  fourth-order tail field and records the low-frequency limitation.
- The `18` coefficient is record 1736's bound using the larger kernel `w`;
  record 3053 uses the exact residual kernel `w-exp(-y/2)` instead.
