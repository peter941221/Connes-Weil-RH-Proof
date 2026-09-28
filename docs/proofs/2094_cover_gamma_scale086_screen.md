# 2094 - Gamma-side scale-0.86 COVER screen

Date: 2026-09-28.

Status: COVER-GAMMA-SCALE086-CANDIDATE.

At delta `0.10`, scale `0.86`, and evaluator `m=6400`, the four registered
heights all have negative finite-window signed Q:

```text
gamma       Q(|xi|<=40)
37.586178   -2.854593150114044e13
40.918719   -1.603831641084071e13
43.327073   -1.518785040476401e14
48.005151   -5.671918720740832e14
```

The same scale is therefore compatible with the registered gamma cells and
with the legal delta-layer readings in record 2093. This is the strongest
sampled COVER pattern so far.

Decision: `COVER-GAMMA-SCALE086-CANDIDATE`. It is not a gamma-uniform theorem:
interpolation between heights, arbitrary heights, delta continuity, and formal
model transfer remain open. The next proof object should be a parameterized
continuity/interval enclosure on the legal half-strip, not another isolated
height scan.

Artifact: `results/2094_cover_gamma_scale086_m6400.json`.
Script: `scripts/routea_cover_gamma_scale086_m6400_2094.py`.