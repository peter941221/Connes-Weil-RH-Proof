# 017 QW--Prolate R1 First Verdict

Date: 2026-07-11

Result: partial. Gate R1 is not rejected, but no QW spectral-selection theorem
has been proved. The first exact defect calculation identifies a possible
analytic producer below the numerical QW/prolate comparison.

## 1. Route Obligation

```text
route obligation:
  select the genuine lowest even eigenvector of A_lambda from the growing
  prolate near-radical cluster

old weak path:
  small Rayleigh value or graphical overlap -> claimed ground-state proximity

new mathematical owner:
  exact Poisson defect and Fourier leakage of the h_0,h_4 prolate combination

consumer to rewire:
  none before a relative QW spectral-projection estimate is proved

forbidden circular inputs:
  RH, global QW positivity, SourceRH, no-off-line zero, detector coverage,
  or an RH-conditioned Weil Hilbert-space factorization

smallest verification target:
  mathematical source audit only; no Lean declaration yet

focused axiom audit:
  none until the defect identity receives a Lean owner
```

## 2. Source-Normalized Objects

Let `P_lambda` be restriction to `[-lambda,lambda]` and let `F` be the
additive Fourier transform with kernel `exp(2*pi*i*x*y)`. Let `p_0` and `p_4`
be normalized even prolate eigenfunctions supported in that interval. Write

```text
P_lambda F(p_0) = chi_0 p_0,
P_lambda F(p_4) = chi_2 p_4.
```

The eigenvalues are real and positive for these two modes, with
`chi_m^2 = nu_m`. The concentration eigenvalues are simple. Source:

```text
Alain Connes
The Riemann Hypothesis: Past, Present and a Letter Through Time
https://arxiv.org/abs/2602.04022
rhready.tex:1118-1135
```

The actual proxy used for Xi is not the old value-zero combination alone. It
is the unique `p_0,p_4` combination with zero integral. Choose the exact
normalization

```text
h_lambda
  := chi_0 * p_0(0) * p_4
       - chi_2 * p_4(0) * p_0.
```

This differs by a nonzero scalar from the source's `h_lambda`. The source
defines `k_lambda = E(h_lambda)` and proves that its transform converges to Xi.
Source: arXiv:2511.22755, `mc2arXiv.tex:1261-1269,1352-1383`.

## 3. Exact Integral And Point Defects

Because zero lies in the support interval,

```text
integral p_0 = F(p_0)(0) = chi_0 p_0(0),
integral p_4 = F(p_4)(0) = chi_2 p_4(0).
```

Therefore the selected combination has zero integral exactly:

```text
integral h_lambda = 0.
```

Its value at zero is not zero at finite `lambda`:

```text
h_lambda(0)
  = p_0(0) * p_4(0) * (chi_0 - chi_2).
```

This is the first exact explanation for the finite-`lambda` failure of the two
Poisson conditions. The source construction imposes the integral condition;
the remaining point defect is governed by the difference of the two prolate
concentration eigenvalues.

## 4. Exact In-Band And Leakage Split

Define the value-zero prolate combination

```text
phi_lambda := p_0(0) * p_4 - p_4(0) * p_0
```

and the out-of-band Fourier leakage

```text
r_lambda := (1 - P_lambda) F(h_lambda).
```

Then the in-band Fourier part is exactly

```text
P_lambda F(h_lambda) = chi_0 * chi_2 * phi_lambda.
```

If the prolate modes are normalized and orthogonal, unitarity of `F` and
orthogonality of their in-band parts give the exact leakage norm

```text
||r_lambda||^2
  = chi_0^2 * |p_0(0)|^2 * (1 - chi_2^2)
      + chi_2^2 * |p_4(0)|^2 * (1 - chi_0^2).
```

Thus both finite defects are controlled by named prolate spectral quantities:

```text
point defect:       chi_0 - chi_2
out-of-band defect: 1 - chi_0^2 and 1 - chi_2^2.
```

The source gives the fixed-mode asymptotic

```text
1 - chi_2
  ~ (2^14 / 3) * sqrt(2) * pi^5
      * exp(-4*pi*exp(L) + (9/2)*L),
L = 2*log(lambda).
```

Source: arXiv:2602.04022, `rhready.tex:1144-1149`.

## 5. Exact Poisson Defect

For a sufficiently regular even function `f`, the full Poisson formula gives

```text
E(f)(u) - E(F(f))(u^-1)
  = (1/2) * (u^-1/2 * F(f)(0) - u^1/2 * f(0)).
```

For `f = h_lambda`, the first correction vanishes because its integral is
zero. If `0 < u < lambda^-1`, then `u^-1 > lambda`; hence the in-band part
`chi_0*chi_2*phi_lambda` contributes nothing to `E(F(h_lambda))(u^-1)`.
Consequently the lower tail of the full summation-map vector has the exact
form

```text
E(h_lambda)(u)
  = E(r_lambda)(u^-1)
      - (1/2) * u^1/2 * p_0(0) * p_4(0) * (chi_0 - chi_2),
  0 < u < lambda^-1.
```

This is stronger than the informal statement that the vector lies near the
global radical. It says precisely which two defects create the part removed by
the support restriction.

The Mellin identity behind the global radical statement is

```text
Mellin(E(f))(z) = zeta(1/2 - i*z) * Mellin(f)(z).
```

The source proves it first by Fubini and then by analytic continuation, with
explicit small- and large-`u` bounds for `E(f)`. Source:

```text
Spectral Triples and Zeta-Cycles
https://arxiv.org/abs/2106.01715
Spectraltriples.tex:1410-1430
```

The zero integral cancels the zeta pole. The nonzero point defect contributes
the explicit `u^1/2` Poisson term above; it does not invalidate the Mellin
factorization at nontrivial zeta zeros.

## 6. What This Does And Does Not Prove

The calculation supplies a plausible lower producer for the observed scale of
the first QW eigenvalue. It does not yet prove:

```text
QW_lambda(k_lambda,k_lambda) has the same leading asymptotic;
k_lambda is close to the first QW eigenspace;
the first QW eigenspace is one-dimensional;
the even bottom lies below the odd bottom;
the coupling to all other near-radical modes is lower order.
```

In particular, `||r_lambda|| -> 0` locates a vector near a defect subspace. It
does not select one eigenvector from the approximately `2*lambda^2` small-mode
cluster.

## 7. Next Rejection Gate

The next theorem must turn the exact lower-tail formula into a QW form or
spectral-projection estimate. The immediate target is a bounded map of the
shape

```text
QW support-tail norm of E(r_lambda)(u^-1)
  <= C_lambda * ||r_lambda||_X,
```

where `X` contains enough regularity for the summation map and where the growth
of `C_lambda` is strictly smaller than the relative gap that selects the first
even state.

R1 is rejected in its current mechanism if every valid bound loses the
exponential or polynomial separation between the first two even prolate
defects, or if coupling to higher near-radical modes is of the same leading
order. Until this comparison is proved, the result remains partial.

## 8. Full-Bottom Warning

Even a successful two-mode or low-cluster theorem does not prove that its
selected state is the ground state of the full `A_lambda`. The omitted
orthogonal complement may contain a negative direction. This distinction is
load-bearing because the selected prolate state is numerically positive and
minuscule.

If one proves along `lambda_j -> infinity` that this positive state is the full
spectral bottom, then

```text
QW_(lambda_j)(f,f) >= 0 for every f in the lambda_j support interval.
```

Every compactly supported Weil test lies in one of these intervals for large
`j`. The result therefore gives global Weil positivity and reaches the RH-level
Weil criterion. This is not a forbidden circular input if proved from lower
analysis, but it shows that full-bottom ownership is itself the main arithmetic
breakthrough. It cannot be inferred from prolate cluster asymptotics alone.
