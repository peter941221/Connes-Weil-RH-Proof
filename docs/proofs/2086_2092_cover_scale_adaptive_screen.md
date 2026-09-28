# 2086-2092 - COVER scale-adaptive delta screen

Date: 2026-09-28.

Status: COVER-SCALE-ADAPTIVE-CANDIDATE, FAR-DELTA-MARGIN-COLLAPSE.

At the G8 height, the sampled signed finite-window values show that the
scale must adapt as delta grows:

```text
delta   scale   Q(|xi|<=40)
0.50    0.88   -6.100510394369240e10
0.50    0.90   -4.089614661700331e10
0.50    0.86   -1.017181568220774e12
0.70    0.86   -9.288438242394230e10
0.70    0.84   -3.349970073708713e11
1.00    0.80   -3.210055975368166e9
```

The scale-adaptive choices improve the margin at the intermediate layers, and
all sampled signs remain negative. At delta `1.00`, however, the absolute
margin has collapsed to `3.21e9`; a fixed absolute L2/EM budget cannot cover
this far-delta regime even though the measured sign survives.

Decision: `COVER-SCALE-ADAPTIVE-CANDIDATE`, with a separate
`FAR-DELTA-MARGIN-COLLAPSE` warning. A viable full COVER route now needs either
relative error bounds that shrink with the signal, or an analytic far-delta
sign theorem. Reusing the center-owner certificate is invalid.

Artifacts: `results/2086_cover_delta04_m6400.json`,
`results/2087_cover_delta05_m6400.json`,
`results/2088_cover_delta05_scale09_m6400.json`,
`results/2089_cover_delta05_scale086_m6400.json`,
`results/2090_cover_delta07_scale086_m6400.json`,
`results/2091_cover_delta07_scale084_m6400.json`, and
`results/2092_cover_delta10_scale080_m6400.json`.