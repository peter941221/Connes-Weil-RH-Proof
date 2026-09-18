# 1641 — Exact Laguerre Fourier columns and the truncation boundary

Date: 2026-09-18

Status: numerical/analytic interface record, not a theorem. This record
supports the healthy-CompactLog B5 carrier consumer only as a candidate
producer study. The carrier base and RH remain open.

## 1. Exact input-column formula

For

```text
h_n(x) = exp(x/2) L_n(-x) 1_{x<0},
```

the Fourier convention used by the carrier probes gives, by the Laplace
transform of the Laguerre polynomial,

```text
H_n(xi) = (-1/2 - 2*pi*i*xi)^n / (1/2 - 2*pi*i*xi)^(n+1).
```

The new script feeds this expression directly into the same half-line
projection and generalized prefix eigenproblem as records 1639 and 1640.
Thus the input-column construction no longer uses a finite spatial grid.

## 2. Cross-check

At `N = 16384`, `d xi = 1/128`, the actual-symbol values are:

```text
lambda   dim=8       dim=10      dim=12      dim=14      observable mass at dim=14
0.2      2.3887e-4   2.3183e-4   1.3805e-4   4.7817e-5   0.9954
0.1      1.6007e-5   2.8899e-6   6.1639e-7   1.5040e-7   0.9231
0.05     3.7015e-6   5.6317e-7   1.0296e-7   2.3824e-8   0.9300
0.02     6.2569e-7   7.7791e-8   1.0841e-8   5.3904e-9   0.9404
```

These agree with the corrected 1640 probe at the relevant displayed scale.
The fixed rank-two rational observable remains macroscopic while the actual
finite-section defect decreases.

## 3. Boundary warning and analytic target

The exact-column model `m = 1, lambda = 1` does not read exactly zero under
the finite FFT projection: at dimensions 8, 10, 12, 14 it reads approximately
`0.992`, `0.990`, `0.988`, and `0.986`. This is a finite-grid half-line
projection/endpoint artifact, not a failure of the Hardy-side model. It means
that the model cannot be used as an exact numerical normalization without an
analytic boundary correction.

The next mathematical target is therefore precise:

1. identify the continuous half-line projection of `exp(2*pi*i*c*xi) m(-xi)
   H_n(xi)`;
2. prove a uniform finite-section-to-continuous estimate for the first fixed
   Laguerre prefixes;
3. only then pass `dim -> infinity` and use the compact-observable interface.

This record strengthens the producer candidate but proves no infinite-
dimensional approximate-kernel statement and changes no route-map conclusion.

## 4. Reproducibility

The exact-column probe is `scripts/carrier_laguerre_exact_1641.py`.
