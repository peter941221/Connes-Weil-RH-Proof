# 2073 - Aggregate Euler-Maclaurin fourth-order probe

Date: 2026-09-28.

Status: EM-FOURTH-ORDER-GO-CANDIDATE.

The same-owner aggregate integrand on `|xi| <= 40` was evaluated without
splitting the visible-prime channels in the error budget. At step `0.005`:

```text
aggregate trapezoid       = -3.406049851781223e12
endpoint EM correction    = -7.953111946906937e-27
finite-difference int|f4| = 1.076581872556369e22
fourth-order remainder    = 9.345328754829594e9
remainder / |value|       = 0.002743743973665674
```

The endpoint correction is negligible because the owner weight is numerically
flat at the finite-window endpoints. The fourth-order remainder proxy is below
both the signed margin and the `4.412215566637855e10` L2 charge.

Decision: `EM-FOURTH-ORDER-GO-CANDIDATE`. This is not yet a proof: the fourth
derivative integral came from finite differences, and no outward rounding,
source-transform enclosure, coefficient enclosure, or model-to-real transfer
has been attached. The next implementation must replace the proxy by a
panelwise interval/jet upper bound for the aggregate fourth derivative while
preserving the aggregate kernel cancellation.

Artifact: `results/2073_finite_window_em_fourth_probe.json`.
Script: `scripts/routea_finite_window_em_fourth_probe_2073.py`.