# Proof 411: Burnol far-tail quadrature audit

Date: 2026-07-19

Status: validity correction for Proof 409.  The previous non-periodic screen
assembled the complete inverse metric from fixed-order quadrature of all
Euler displacements.  The far cosine blocks have frequency
`2 pi exp(abs(z))`, so that computation does not resolve the tail.  The
resulting matrix can be non-Hermitian and indefinite even though the exact
metric is a positive Hermitian compression.  Therefore the numerical
response table in Proof 409 is not obstruction evidence and is withdrawn as a
quantitative claim.

## 1. Exact positivity requirement

Let `A` be the Burnol boundary synthesis map and let `nu_S` be the complete
normalized Euler inverse law.  The metric used by the route is

```text
G_S = integral A* U_z A d nu_S(z).
```

The symmetric geometric-difference law is the positive Poisson kernel of the
normalized inverse factor.  Consequently `G_S` is Hermitian positive
semidefinite.  Any finite computation that is used inside `G_S^(-1)` must at
least preserve this structural test up to a declared truncation and
quadrature error.

For a geometric tail of omitted mass `delta`, the unitary bound gives the
operator estimate

```text
|| integral_(tail) A* U_z A d nu_S(z) ||
  <= delta ||A||^2.
```

The bound is useful even before a continuous estimate: a negative eigenvalue
far larger than `delta ||A||^2`, or a large Hermitian defect, cannot be
explained by the omitted probability mass alone.

The positivity input is the unitary-translation structure of Burnol's
boundary construction; see Burnol, Theorem 8 and the surrounding transform
identities: `https://arxiv.org/abs/math/0208121`.

## 2. Failure mechanism in Proof 409

The cosine rectangle in the screen is evaluated as

```text
2 sqrt(rho) cos(2 pi rho x y),   rho=exp(z).
```

The fixed Gauss-Legendre rule integrates this block with an order independent
of `rho`.  With prime-power cutoff `m`, the largest frequency is roughly

```text
2 pi exp(m log(p)) = 2 pi p^m.
```

Thus increasing the geometric cutoff increases the unresolved frequency
exponentially while the quadrature order stays fixed.  The far part must be
handled analytically (or with an error-controlled oscillatory quadrature)
before inverting the averaged metric.

## 3. Reproducible audit

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/411_burnol_far_quadrature_audit.py
```

The probe checks the approximate metric's Hermitian defect and smallest
eigenvalue, then reports the response produced by the same `409` assembly.
Its default output has the following representative rows (size `6`, primes
`2,3,5,7`, grid step `0.2`):

```text
+------+-------+-------------+-----------+-----------+-------------+-------------+
| power| order | max frequency| tail mass | herm error| min eig     | response    |
+------+-------+-------------+-----------+-----------+-------------+-------------+
|  8   |  32   | 2.97e19      | 6.20e-2   | 5.63e-2   | -8.87e-1    | unstable    |
|  8   | 128   | 2.97e19      | 6.20e-2   | 1.02e-2   | -1.36e-1    | unstable    |
| 10   |  32   | 1.46e24      | 2.91e-2   | 2.61e-1   | -1.72e0     | unstable    |
| 10   | 128   | 1.46e24      | 2.91e-2   | 1.21e-1   | -2.59e-1   | unstable    |
+------+-------+-------------+-----------+-----------+-------------+-------------+
```

For cutoff `10`, the negative eigenvalue at quadrature order `128` is about
`0.259`, while the omitted mass is only `0.0291`; the Hermitian defect is
about `0.121`.  Raising the order to `192`, `256`, and `384` changes the
negative eigenvalue to approximately `-0.316`, `-0.292`, and `-0.157` rather
than producing convergence.  The same screen's normalized near response at
orders `32,64,96,128,192,256` is approximately

```text
0.4435, 0.4163, 0.4489, 0.4071, 0.3826, 0.3823,
```

for this finite cohort.  That variation is a numerical-resolution signal,
not a source-specific lower bound.

## 4. Consequence for Proofs 409--410

Proof 409's prime-set stabilization is not sufficient evidence because the
same unresolved far metric is reused for every prime set.  The positive
metric audit fails before the inverse-after-average scalar can be interpreted.
Proof 410's continuous theorem contract remains the right mathematical target,
but its numerical "survivor" label must be downgraded to unverified.

The valid order is now:

```text
far oscillatory metric / half-density residue
  -> error-controlled positive `G_S`
  -> complete inverse-after-average near response
  -> one final absolute value.
```

Do not infer Gate 3U failure from the old `409` table, and do not use the
screen as evidence for a continuous counterexample.  The analytic near
estimate and the finite-`S` sign remain open.

## 5. Route judgment

```text
Proof 409 finite response table       withdrawn as uncertified;
far metric positivity audit           fails fixed-order quadrature;
continuous Burnol near theorem        open;
Gate 3U / finite-S sign / Burnol / RH open / open / open / open.
```
