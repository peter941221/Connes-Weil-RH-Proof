# 1851 - All-index healthy orbit assembly

Date: 2026-09-22.

Status: Formally verified in Lean 4; producer-side interface progress only.

The theorem
`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets_all_indices`
keeps the base and residual correction fixed after the nearby-zero radius is
chosen. For every later orbit count `n` satisfying the explicit quadratic-tail
condition, it reconstructs on the same selected owner:

```text
support, raw target values, minimal interpolation,
centered orbit sum = -2, square-zero control,
source tail < epsilon, and convolution-square tail < epsilon^2.
```

The theorem is built from the fixed-correction assembly record 1850 and the
existing same-owner transport lemmas. It removes the producer's existential
index mismatch at the healthy-orbit layer, but it does not prove the strict
base contraction, the geometric budget, or detector-specific semi-local
positivity.

Verification: focused Lake build log `1851_all_indices_raw.log`, successful
footer, zero `error:` lines; the paired Probe prints the new theorem's axioms.
