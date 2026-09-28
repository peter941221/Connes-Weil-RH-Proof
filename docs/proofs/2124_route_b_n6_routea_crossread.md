# 2124 — Route-A cross-read for the n=6 candidate

Date: 2026-09-28.

Status: ROUTE-A-COVERAGE-PASS, numerical cross-read only. The prime-channel
interpolation error is not yet certified, and no producer or RH claim follows.

For the record-2123 `n=6` owner, the full visible-prime book has `595877`
entries and support radius `16`. On both registered grids the largest
`log(q)` is below the FFT Nyquist frequency, so the phased FFT route has full
coverage rather than a truncated prime sum:

```text
dxi=0.02   Nyquist=24.9900   max log(q)=15.99999983   coverage=1.0
dxi=0.01   Nyquist=49.9900   max log(q)=15.99999983   coverage=1.0
```

The direct finite sum is the B-route reference; the phased FFT plus cubic
spline is the Route-A cross-read. Relative A/B differences in the three prime
moments are:

```text
             C-prime       b-prime       D-prime
dxi=0.02     1.87e-4       1.54e-4       1.49e-4
dxi=0.01     3.16e-4       2.31e-4       2.03e-4
```

After adding the archimedean channel, the full gate remains negative on both
routes:

```text
             B determinant        A determinant       rel A/B
dxi=0.02     -5.1064396e19        -5.1052018e19       2.42e-4
dxi=0.01     -5.0951609e19        -5.0936387e19       2.99e-4
```

This is useful evidence because the Route-A FFT does not lose the high prime
book. It is not a certificate: the cubic-spline interpolation and the DFT
rounding still need an explicit one-sided error bound that is smaller than the
`C`, `b`, and determinant margins.

Next target:

```text
bound Route-A prime moment error
    -> propagate it to C, b, D, det
    -> preserve C > 0, b > 0, det < 0
    -> retain the n=6 tail margin
```
