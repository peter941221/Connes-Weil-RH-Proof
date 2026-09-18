# 1642 — Continuous exact model matrix for the Laguerre probe

Date: 2026-09-18

Status: exact model calibration and analytic target, not a theorem for the
Gamma multiplier. It supports the healthy-CompactLog B5 carrier consumer as
a producer study; the carrier base and RH remain open.

## 1. Continuous model identity

For `m = 1`, write `c = 2 log(lambda)`. Multiplication by
`exp(2*pi*i*c*xi)` translates the inverse Fourier transform. With the
projection orientation used by the carrier probe, the defect Gram matrix on
the degree prefix `0,...,d-1` is exactly

```text
M_ij(c) = integral_{-infinity}^c h_i(y) h_j(y) dy
         = integral_{-c}^infinity exp(-t) L_i(t) L_j(t) dt.
```

The full Laguerre Gram matrix is the identity. Thus the smallest continuous
model defect is the square root of the smallest eigenvalue of `M(c)`; no FFT,
spatial window, or half-line pixelization is involved.

## 2. Exact quadrature readback

Adaptive vector quadrature with absolute and relative tolerance `1e-13` gives:

```text
lambda   dim=8       dim=10      dim=12      dim=14
0.2      5.4049e-4   1.7428e-4   6.2267e-5   2.4066e-5
0.1      7.4414e-5   1.9080e-5   5.5382e-6   1.7675e-6
0.05     1.2996e-5   2.7458e-6   6.6846e-7   1.8158e-7
0.02     1.6347e-6   2.7705e-7   5.5620e-8   1.2014e-8
```

The quadrature error reported by the integrator is below `1e-12` in all
rows. Compared with the exact-column finite FFT probe, the FFT model values
are larger, as expected from the finite-grid boundary error. The continuous
model is therefore the correct normalization for future comparisons.

## 3. Consequence for the actual symbol

At the same finite degree and scale, the actual Gamma-symbol readback is
approximately `1.50e-7` at `lambda = 0.1`, versus the continuous free-shift
model value `1.77e-6`. The observed ratio is about `0.085`, consistent with
the earlier position-law measurements and with a genuine focusing effect of
the multiplier. This is still numerical evidence; it is not an operator
inequality.

The next analytic task is now sharply stated: express the actual matrix

```text
<P_- U_lambda H_i, P_- U_lambda H_j>
```

as the continuous free-shift incomplete-Gamma matrix plus a controlled
Gamma-symbol correction, uniformly in the degree prefix. A proof of a
finite-prefix contraction is not enough; the correction must be controlled as
the prefix dimension grows so that the 1636 compact-observable interface can
be invoked.

## 4. Reproducibility

The calibration script is `scripts/carrier_laguerre_model_exact_1642.py`.
