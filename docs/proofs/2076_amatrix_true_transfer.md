# 2076 - True a_mat transfer on the selected owner

Date: 2026-09-28.

Status: AMATRIX-TRANSFER-GO-CANDIDATE.

The stored `17 x 17` family-value matrix was replaced by a 50-digit
mpmath-Laplace reconstruction at every owner node, then the base and
correction coefficient solves were repeated. The largest entry gap is
`3.335450987703283e-23`; the Frobenius gap is `3.3844191356463986e-23`.

The signed finite-window Q moved by:

```text
stored a_mat -> true a_mat = 4.194993408203125e4
transfer / |Q|             = 1.2316300553800175e-8
```

The true-matrix reading is `-3.406049842817425e12` at step `0.02` and
`-3.406049842817794e12` at step `0.01`.

Decision: `AMATRIX-TRANSFER-GO-CANDIDATE`. This is a measurement, not an
interval transfer: mpmath quadrature and the stored coefficients still need
formal outward certificates. It nevertheless prices the named `a_mat`
idealisation gap far below the available signed margin.

Artifact: `results/2076_amatrix_true_transfer.json`.
Script: `scripts/routea_amatrix_true_transfer_2076.py`.