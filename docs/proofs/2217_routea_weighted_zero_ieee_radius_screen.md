# 2217 — Full-node IEEE-style AMP radius screen

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector on the actual
source-zero owner; the downstream producer target remains same-owner
`qw >= 0`.

The 2211 exponent/operation allowance was rerun over all 30 interpolation
nodes, all 30 families, and the same `NSEG=1100`, 12-panel Simpson rule used
by the 2209/2210 candidate screen. Under the explicit standard forward-error
model (`U = eps/2`, AMP factor `8U`, operation factor `16U`), the result is:

```text
minimum total radius       5.294892110768219e-10
maximum total radius       2.459424789942387e-08
binding node                2  (0.9450000000000001 - 39.25244858548658 i)
binding row                 2.459424789942387e-08
```

The maximum is exactly the previously identified binding row to displayed
precision; the full-node run found no hidden spike. The result therefore
closes the scope gap in 2211 and preserves the combined correction price
`6.2550323e-5` used by the candidate margin screen.

Status: `FULL-NODE-FORWARD-RADIUS-SCREEN-GO /
OUTWARD-IEEE-CERTIFICATE-OPEN`.

This is a reproducible parameterized forward-error price, not a proof that
NumPy operations satisfy those radii, not a complete-owner transfer, and not
a producer theorem. No RH claim follows.

Artifact and log:

- `results/2217_weighted_zero_ieee_radius.json`
- `results/20260929_2217_ieee_radius_screen_pass2.log`
- script: `scripts/routea_weighted_zero_ieee_radius_2217.py`
