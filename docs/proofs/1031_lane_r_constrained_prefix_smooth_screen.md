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

## Candidate certificate

Let

```text
B(g) = ( L(g,0), L(g,1/2), L(g,1) )
```

where `L(g,s)` is the bilateral Laplace transform.  The screen tests the
stronger rank-three inequality

```text
P_21(g) <= |L(g,0)|^2 + |L(g,1/2)|^2 + |L(g,1)|^2.
```

On the three-node nullspace the right-hand side is zero, so this certificate
would imply the fixed-prefix target directly.  The coefficient `1` is a
simple candidate selected by the screen; it is not asserted in Lean.

## Method

- Base support is `[-r,r]`, with `2*r < log(2)` so the square is prime-free.
- The base functions are `Legendre_k(t/r) * exp(-1/(1-(t/r)^2))^p` for
  `p = 1, 2`, extended by zero outside the interval.
- Simpson quadrature imposes selected real Laplace constraints, and a separate
  rectangle-rule Gram matrix L2-orthonormalizes the resulting nullspace.
- The reported `full_pos` is the number of positive eigenvalues in the
  *unconstrained sampled matrix*.  It is not an operator-index theorem.
- `cert_max` evaluates `P_21 - B^T B` on the full sampled basis, while
  `lambda_star` is the smallest sampled scalar coefficient in `P_21 -
  lambda * B^T B` that reaches nonpositivity.  Both are finite numerical
  diagnostics.

## Representative results

All rows use `r = 0.3464`, so the square support is `0.6928`, strictly below
`log(2) = 0.693147...`.  The `prefix_max` column is the largest constrained
eigenvalue; negative is the desired numerical sign.  The certificate columns
are computed on the corresponding *unconstrained* full basis.

```text
+----------------+----+----+---------+-------------+----------+------------+------------+------------+
| constraints    | p  | K  | nullity | prefix_max  | full_pos | full_max   | cert_max   | lambda_star|
+----------------+----+----+---------+-------------+----------+------------+------------+------------+
| 0, 1/2, 1      | 1  | 16 |      13 | -0.8425865  |        1 | +1.199122  | -0.108248  | 0.707327   |
| 0, 1/2, 1      | 1  | 32 |      29 | -0.8200490  |        1 | +1.231174  | -0.084081  | 0.723556   |
| 0, 1/2, 1      | 1  | 48 |      45 | -0.8104713  |        1 | +1.244280  | -0.073817  | 0.732830   |
| 0, 1/2, 1      | 1  | 56 |      53 | -0.8074083  |        1 | +1.248421  | -0.070534  | 0.736218   |
+----------------+----+----+---------+-------------+----------+------------+------------+------------+
```

The one-node screens are useful diagnostics, not a replacement theorem: their
high-frequency margin shrinks substantially.  Keeping all three existing
Lane R constraints gives a much more stable sampled gap near `-0.8`.  The
unconstrained positive index is one in these finite screens, but that pattern
is not an operator-index theorem.

## Consequence for the proof route

The productive next Lean statement is not another absolute-tail adapter.  It
is an analytic proof of the candidate rank-three certificate, or a stronger
continuous kernel inequality implying it, on the full prime-free interval.
Such a certificate must control the full compactly supported function space;
the finite-grid spectra and the observed `lambda_star` values cannot be
imported as proof data.

## Reproduction

```text
python docs/proofs/1031_lane_r_constrained_prefix_smooth_screen.py \
  --grid-size 6001 --radii 0.34 0.3464 \
  --basis-sizes 8 12 16 24 32 --envelope-powers 1 2 \
  --penalty-coefficient 1

python docs/proofs/1031_lane_r_constrained_prefix_smooth_screen.py \
  --grid-size 8001 --radii 0.3464 --basis-sizes 40 56 \
  --envelope-powers 1 --constraint-nodes 0 0.5 1 \
  --penalty-coefficient 1
```
