# 1021 - Gamma_R paired-profile term screen

Date: 2026-08-18.

Probe: `docs/proofs/1021_lane_r_gamma_profile_term_screen.py`.

## Verdict

The tempting termwise route is rejected.  Even on the triple-vanishing
prime-free subspace, sufficiently large individual Gamma_R paired-profile
summands have positive directions.  The negative total archimedean form seen
in 1020 must therefore use cancellation between the constant term and the
profile series (and/or between different profile indices).

This is a numerical route screen, not a Lean theorem and not an RH result.

## Exact Numerical Object

For a real `g` supported in `[-r,r]`, the `n`-th paired profile contributes the
quadratic form

```text
J_n(g) = integral integral exp(-(2*n+1/2)*|x-y|) g(x) g(y) dx dy
         - 2/(2*n+1) * integral g(x)^2 dx.
```

The probe uses a sine basis on `[-r,r]`, projects onto the nullspace of
`laplaceAt(g,0)`, `laplaceAt(g,1/2)`, and `laplaceAt(g,1)`, and evaluates the
double integral by integrating the inner variable analytically.  Only the
remaining smooth outer integral uses Gauss-Legendre quadrature.  This matters:
for large `n`, the two displayed terms nearly cancel and both a lag-grid
convolution and a raw two-dimensional quadrature can manufacture a false sign.

For `omega_k = k*pi/(2*r)`, the inner action on the `k`-th sine basis function
is evaluated as

```text
H_k(y) = [2*a*sin(omega_k*(y+r))
          + omega_k*exp(-a*(y+r))
          - omega_k*(-1)^k*exp(-a*(r-y))] / (a^2 + omega_k^2),
```

where `a = 2*n + 1/2`.

Command:

```text
python docs/proofs/1021_lane_r_gamma_profile_term_screen.py \
  --radius 0.345 --basis-size 16 --quadrature-size 1200
```

The square support radius is `0.690`, below `log(2) = 0.693147180560`, so
the test is in the prime-free regime.

## Results

At radius `r = 0.345`, basis size `16`, and quadrature size `1200`:

```text
+-------+------------------+------------------+--------------------+
| n     | lambda_min       | lambda_max       | verdict            |
+-------+------------------+------------------+--------------------+
| 0     | -1.9997985e+00   | -1.9943782e+00   | nonpositive        |
| 1     | -6.6566057e-01   | -6.3997754e-01   | nonpositive        |
| 2     | -3.9819543e-01   | -3.5660036e-01   | nonpositive        |
| 5     | -1.7769434e-01   | -1.1565249e-01   | nonpositive        |
| 10    | -8.7687913e-02   | -3.2266022e-02   | nonpositive        |
| 20    | -3.6692864e-02   | -5.9939332e-03   | nonpositive        |
| 40    | -1.0822297e-02   | -8.2882736e-04   | nonpositive        |
| 80    | -2.0496738e-03   | -9.2145189e-05   | nonpositive        |
| 120   | -6.6987151e-04   | -2.2142932e-05   | nonpositive        |
| 200   | -1.5142974e-04   | -2.3744993e-06   | nonpositive        |
| 400   | -1.8719907e-05   | +4.7718220e-07   | positive direction |
| 800   | -2.1661977e-06   | +2.5456279e-07   | positive direction |
+-------+------------------+------------------+--------------------+
```

The moment residual was `2.8e-17` and the L2 orthonormality error was below
`5e-16` at quadrature size `3000`.  The `n = 400` and `n = 800` values were
unchanged to the displayed digits at quadrature sizes `600`, `1800`, and
`3000`.  The positive values are small because the profile is a large-index
resolvent difference, but they are stable after the analytic inner integral.

## Route Consequence

The exact Gamma_R declarations in `C1XiCenterTwoGamma` remain useful:

```text
integralOn_archimedeanIntegrand_eq_tsum
normalized_gammaR_centerTwo_re_eq_archimedeanTerm
```

They provide the correct same-owner readback.  They cannot be consumed with a
lemma of the form `forall n, J_n(g) <= 0`, because this screen supplies a
counterexample direction for large `n`.  The next viable analytic target is a
sign estimate for the *summed* kernel on the three-moment subspace, with its
constant term and tail retained together.

This does not weaken the 1020 total-form scan: a sum can be negative while
some summands are positive.  It narrows the formalization target and prevents
a false termwise Gamma proof.  The prime-inclusive Lane R case, global
spectral nonnegativity, and RH remain open.
