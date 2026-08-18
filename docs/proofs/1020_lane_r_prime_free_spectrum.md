# 1020 - Lane R prime-free archimedean spectrum scan

Date: 2026-08-18.

Probe: `docs/proofs/1020_lane_r_prime_free_spectrum.py`.

## Verdict

The deterministic scan supports a negative-definite archimedean quadratic
form on the tested triple-vanishing, prime-free subspaces.  The result is
numerical evidence only.  It is not a Lean theorem, a detector construction,
or an RH proof.

The strongest independent check uses a sine basis, which has no bump-envelope
choice and is well-conditioned under the sampled L2 inner product.  At the
prime-free boundary approached here, `r = 0.345` gives square support radius
`2*r = 0.690`, while `log(2) = 0.693147180560`.

## Object And Method

For a real test `g` supported in `[-r, r]`, the Hermitian convolution square
is supported in `[-2*r, 2*r]`.  Thus `2*r < log(2)` removes every finite
prime-power term.  The three rows of the constraint matrix impose

```text
laplaceAt(g, 0)   = 0
laplaceAt(g, 1/2) = 0
laplaceAt(g, 1)   = 0.
```

The probe forms the same archimedean term used by the Lean owner:

```text
arch(F) = (log(4*pi) + EulerGamma) * F(0)
          + integral_{y>0}
              (exp(y/2) * (F(y) + F(-y)) - 2*F(0)) / (2*sinh(y)) dy.
```

It computes the quadratic-form matrix on the constraint nullspace after L2
orthonormalization, then reports its smallest and largest eigenvalues.  The
tail beyond the compact square support is integrated analytically.

The WSL2 command used for the independent sine-basis scan was:

```text
python docs/proofs/1020_lane_r_prime_free_spectrum.py \
  --grid 6001 --radii 0.20 0.30 0.345 \
  --basis-sizes 8 16 24 32 48 --basis-families sine
```

## Results

Sine basis, grid size 6001:

```text
+--------+----+------------+------------+----------+----------+----------------------+
| r      | K  | lambda_min | lambda_max | residual | orth err | verdict              |
+--------+----+------------+------------+----------+----------+----------------------+
| 0.200  |  8 |  -2.25124  |  -1.42488  | 1.5e-17  | 4.5e-16  | negative definite    |
| 0.200  | 48 |  -4.08890  |  -1.39984  | 3.1e-17  | 6.7e-16  | negative definite    |
| 0.300  |  8 |  -1.84571  |  -1.01882  | 3.1e-17  | 5.3e-16  | negative definite    |
| 0.300  | 48 |  -3.68345  |  -0.99371  | 3.1e-17  | 8.9e-16  | negative definite    |
| 0.345  |  8 |  -1.70591  |  -0.87870  | 2.8e-17  | 6.2e-16  | negative definite    |
| 0.345  | 48 |  -3.54370  |  -0.85356  | 3.4e-17  | 8.9e-16  | negative definite    |
+--------+----+------------+------------+----------+----------+----------------------+
```

Grid convergence at the widest tested support and `K = 48`:

```text
+------+------------+----------+----------+----------------------+
| grid | lambda_min | lambda_max | residual | verdict              |
+------+------------+----------+----------+----------------------+
| 3001 |  -3.54321  |  -0.85361  | 3.5e-17  | negative definite    |
| 6001 |  -3.54370  |  -0.85356  | 3.4e-17  | negative definite    |
|12001 |  -3.54381  |  -0.85353  | 3.0e-17  | negative definite    |
+------+------------+----------+----------+----------------------+
```

The independent Legendre-times-bump family also stayed negative through
`K = 32`, and powers `1`, `2`, and `4` of the smooth envelope preserved the
sign.  Its coefficient Gram matrix becomes ill-conditioned at high degree;
the sine results above are the preferred stability check.

## Route Boundary

`C1XiCenterTwoGamma` already proves the exact Gamma_R paired-profile readback
through `integralOn_archimedeanIntegrand_eq_tsum` and
`normalized_gammaR_centerTwo_re_eq_archimedeanTerm`.  Those theorems identify
the correct series owner but do not prove a sign for the series on the
three-moment nullspace.  The next formal target is therefore an actual
prime-free sign inequality, not a transport of these numerical eigenvalues.

The sign direction remains:

```text
arch(g^2) <= 0  ->  qw(g) >= 0       (Lane R positivity)
arch(g^2) >  0  ->  detector-side positivity (needed for an off-line zero)
```

The prime-inclusive Lane R case and global spectral nonnegativity remain
open.  RH is not claimed.
