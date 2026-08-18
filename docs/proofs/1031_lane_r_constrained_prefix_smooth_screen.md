# 1031 - Smooth screen for the Lane R constrained prefix

Date: 2026-08-19.

Probe: `docs/proofs/1031_lane_r_constrained_prefix_smooth_screen.py`.

## Verdict

The fixed `N = 21` Gamma_R prefix remains strictly negative in independent
smooth compact-support screens up to the prime-free boundary.  The numerical
evidence is materially stronger than the earlier sine-only scan because each
test function is a Legendre polynomial times a C-infinity bump, so its zero
extension has the regularity required by the Lean test owner.

This is still numerical evidence only.  It does not prove
`laneRConstrainedPrefixSignTarget`, a tail sign, universal Lane R, global
spectral nonnegativity, or RH.

## Exact screened form

For a real compactly supported test `g`, put `F = g^* * g`, let

```text
a_n = 2 n + 1/2
b_n = 2 n + 1
C   = log(4*pi) + EulerGamma.
```

The exact real `N`-prefix is the quadratic form

```text
P_N(g) = C ||g||_2^2
       + sum_{n < N} (
           double_integral g(x) exp(-a_n |x-y|) g(y) dx dy
           - 2 / b_n ||g||_2^2).
```

This is the real specialization of the same paired profile owned by
`gammaRArchFinitePrefixValue`.  The script evaluates the resolvent matrix
above and independently checks its top eigenvector by direct autocorrelation
of `F`.

## Method

- Base support is `[-r,r]`, with `2*r < log(2)` so the square is prime-free.
- The base functions are `Legendre_k(t/r) * exp(-1/(1-(t/r)^2))^p` for
  `p = 1, 2`, extended by zero outside the interval.
- Simpson quadrature imposes selected real Laplace constraints, and a separate
  rectangle-rule Gram matrix L2-orthonormalizes the resulting nullspace.
- The reported `full_pos` is the number of positive eigenvalues in the
  *unconstrained sampled matrix*.  It is not an operator-index theorem.

## Representative results

All rows use `r = 0.3464`, so the square support is `0.6928`, strictly below
`log(2) = 0.693147...`.  The `prefix_max` column is the largest constrained
eigenvalue; negative is the desired numerical sign.

```text
+----------------+----+----+---------+-------------+----------+------------+
| constraints    | p  | K  | nullity | prefix_max  | full_pos | direct diff |
+----------------+----+----+---------+-------------+----------+------------+
| 0, 1/2, 1      | 1  | 24 |      21 | -0.8283769  |        1 | 8.93e-13   |
| 0, 1/2, 1      | 1  | 40 |      37 | -0.8144911  |        1 | 8.70e-12   |
| 0, 1/2, 1      | 1  | 56 |      53 | -0.8074099  |        1 | 2.12e-09   |
| 0, 1/2, 1      | 2  | 40 |      37 | -0.8351858  |        1 | 1.70e-09   |
| 0              | 1  | 32 |      31 | -0.1133544  |        1 | 5.08e-13   |
| 1/2            | 1  | 48 |      47 | -0.0910110  |        1 | 6.06e-12   |
| 1              | 1  | 48 |      47 | -0.0569410  |        1 | 1.91e-10   |
| 0, 1/2         | 1  | 48 |      46 | -0.5435145  |        1 | 5.84e-10   |
+----------------+----+----+---------+-------------+----------+------------+
```

The one-node screens are useful diagnostics, not a replacement theorem: their
high-frequency margin shrinks substantially.  Keeping all three existing
Lane R constraints gives a much more stable sampled gap near `-0.8`.

## Consequence for the proof route

The productive next Lean statement is not another absolute-tail adapter.  It
is an analytic certificate for the continuous quadratic kernel on the
prime-free interval, for example a rank-three correction whose restriction to
the three Laplace-moment nullspace is nonpositive.  Such a certificate must
control the full compactly supported function space; the finite-grid spectra
above cannot be imported as proof data.

## Reproduction

```text
python docs/proofs/1031_lane_r_constrained_prefix_smooth_screen.py \
  --grid-size 6001 --radii 0.34 0.3464 \
  --basis-sizes 8 12 16 24 32 --envelope-powers 1 2

python docs/proofs/1031_lane_r_constrained_prefix_smooth_screen.py \
  --grid-size 8001 --radii 0.3464 --basis-sizes 40 56 \
  --envelope-powers 1 --constraint-nodes 0 0.5 1
```
