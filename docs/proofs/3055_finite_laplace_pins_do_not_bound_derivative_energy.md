# Finite Laplace pins do not bound derivative energy (record 3055)

Date: 2026-10-19.

Status: scoped paper-level counterfamily for the support-and-interpolation
API. It is not a no-go for the complete `OrbitG8Geometry`, whose spectral-tail
field is an additional constraint.

## Claim

Fix a nonempty bounded open interval `I`, a finite set of complex Laplace
nodes `S`, and any compactly supported smooth complex test `f0` supported in
`I`. For each `s` in `S`, prescribe the value `L(f0,s)`. Among smooth tests
supported in `I` with exactly those same Laplace values, the ratio

```text
integral_I |f'(x)|^2 dx / integral_I |f(x)|^2 dx
```

has no finite upper bound (provided the interpolation class contains a
nonzero member). Thus support and finitely many exact interpolation values
alone cannot imply the low-band/derivative-energy bound needed by record 3053.

## Nullspace carrier construction

Choose a nonzero `psi` in `C_c^infinity(I)` and enumerate the finite nodes as
`S={s_1,...,s_m}`. For a positive integer carrier frequency `N`, set

```text
u_N(x) = exp(-i*N*x) * psi(x)

D_s h = h' + s*h
h_N = N^(-m) * D_{s_m} ... D_{s_1} u_N.
```

Every derivative preserves compact support, so `h_N` is supported in `I`.
Integration by parts gives the exact transform law

```text
L(D_s h, z) = (s-z) * L(h,z).
```

Consequently `L(h_N,s_j)=0` for each node `s_j`, with no approximation.

Expanding the differential product after factoring out `exp(-i*N*x)` gives

```text
h_N(x) = exp(-i*N*x) * (c*psi(x) + O_H1(1/N)),
|c| = 1.
```

Here `O_H1(1/N)` means a remainder whose function and first derivative have
`L2` norms bounded by a constant times `1/N`; this follows because the
highest carrier power is `(-i*N)^m`, while every lower polynomial term has
degree at most `m-1`. Therefore

```text
||h_N||_2 -> ||psi||_2,
||h_N'||_2 / N -> ||psi||_2.
```

For `f_N=f0+h_N`, the Laplace values at all nodes are unchanged. The
Riemann-Lebesgue lemma makes the mass cross term with fixed `f0` tend to zero,
while `||f_N'||_2/N -> ||psi||_2`; hence

```text
||f_N'||_2^2 / ||f_N||_2^2 -> infinity.
```

This construction changes no support endpoint and preserves every pinned
Laplace value exactly. It exposes why finite interpolation alone cannot
control a continuum band integral: finitely many point evaluations leave an
infinite-dimensional nullspace containing arbitrarily rapid oscillations.

## Boundary: full geometry is not ruled out

`OrbitG8Geometry` also requires a `FourthOrderSpectralTail` for the
convolution square. The carrier perturbation above is not shown to preserve
that tail. In fact, record 3054 shows that the tail constrains high-frequency
mass, so it may exclude this particular sequence. Record 3055 therefore rules
out only a derivation from support plus finite Laplace pins; it does not rule
out combining those data with the complete same-owner tail constraint.

One possible intermediate lemma is a low-frequency estimate that consumes
both:

```text
finite interpolation pins + exact FourthOrderSpectralTail
        -> bound on integral_{|t|<T_*} t^2*|L g(i*t)|^2 dt
        -> derivative-energy ratio D/M
        -> record-3053 continuous-term threshold
```

This can help price a term in the full joint-symbol balance, but it is not the
Route-A acceptance target. Record 3056 identifies that target as positive-band
credit dominating negative-band deficit on the same owner.

The derivative-shift transform law is already formal in
`C1LaneRD3Root.laplaceAt_derivativeShift`; the asymptotic `L2` carrier argument
above is not yet formalized in Lean. No selected-owner no-go, signed
discrepancy estimate, or RH conclusion follows.

Evidence:

- `ConnesWeilRH/Dev/C1LaneRD3Root.lean` proves
  `L(D_s h,z)=(s-z)L(h,z)` for compact-log tests.
- `ConnesWeilRH/Dev/C1HealthyYoshidaCorrectionFamily.lean` records the
  support-plus-finite-Laplace-value correction API and explicitly stores no
  derivative-energy or sign field.
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` shows that the full geometry has
  the additional `raw_square_tail` field, which this counterfamily does not
  preserve.
- `docs/proofs/3054_fourth_order_tail_to_derivative_energy.md` records the
  tail's high-frequency consequence and the remaining low-frequency gap.
