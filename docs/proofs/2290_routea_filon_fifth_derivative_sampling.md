# 2290: fifth-derivative sampling refinement for Filon 24:4

Date: 2026-09-30

Decision: the 24:4 phase-aware Filon candidate survives a denser fifth-derivative sampling screen; uniform certification remains open.

## Method

The candidate from 2289 uses 24 panels and degree 4, so its Lagrange residual uses the fifth derivative of the complete corrected owner amplitude. This record samples that derivative at 3, 9, and 33 interior points per panel, preserving the full family sum before taking the modulus.

## Result

```text
samples/panel       base price       corr price       combined
3                   1.8145e6         1.5000e6         3.3143e6
9                   2.5034e6         1.5000e6         4.0031e6
33                  2.5553e6         1.5470e6         4.1023e6
```

The denser screen increases the base price by about 40.7% and the correction price by about 3.2%, but does not reveal an order-of-magnitude hidden peak. The 33-point combined price remains below `1e7`.

## Next gate

This is still not a uniform derivative enclosure. The next implementation must replace sampled maxima by a directed interval or analytic panel bound for the fifth derivative, then propagate the resulting transform error through the actual kernel-weighted quadratic functional. The current `4.1023e6` is only a candidate amplitude-residual price.

## Nonclaims

- Sampled maxima are not uniform derivative enclosures.
- No finite-window quadrature certificate or hgap supplier exists yet.
- The infinite xi tail is separate.
- No producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_filon_fifth_derivative_sampling_2290.py
python -m unittest discover -s scripts -p 'routea_filon_fifth_derivative_selftest_2290.py' -v
```
