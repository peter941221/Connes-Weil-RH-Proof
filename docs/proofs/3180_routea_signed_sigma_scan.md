3180 Route-A Signed Sigma Scan
=============================

Status
------

SIGNED_SIGMA_SCAN_DIAGNOSTIC

This scan keeps the current owner coefficients, bump functions, frequency
support, and signed real-part evaluation unchanged. It varies only the height
weight parameter sigma over a small diagnostic range. The purpose is to test
whether the positive finite-window result at sigma `-0.5` and `+0.5` is an
isolated parameter choice or persists across the nearby admissible family.

The scan uses composite trapezoid integration. It has no curvature enclosure,
so it is not a certified integral bound and cannot feed the Lean producer.

Reproduction
------------

```text
python scripts/routea_signed_sigma_scan_3180.py
```

The machine-readable result is:

```text
results/3180_signed_sigma_scan.json
```

Observed result
---------------

The default scan evaluates 21 points from sigma -1 through 1 in steps of
0.1. It finds zero negative points. The smallest sampled midpoint is about
0.9998851713213382 near sigma 0, and the largest is about
1.0000487331632203 near sigma -0.8.

This strengthens the 3179 replay: within this sampled height-weight range,
changing sigma does not expose a negative candidate. It is still not a
theorem about all sigma values or all owners.

Interpretation rule
-------------------

`negative_count > 0` would identify a candidate sigma that needs a separate
rigorous enclosure. `negative_count = 0` records only a diagnostic failure of
this parameter scan; it does not prove that every owner or correction fails.
