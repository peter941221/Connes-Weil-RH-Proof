# 2082/2085 - COVER delta margin screen

Date: 2026-09-28.

Status: COVER-DELTA-SAMPLED-NEGATIVE.

At the G8 height, the m=6400 finite-window signed readings at scale `0.88`
are:

```text
delta       Q(|xi|<=40)
0.05       -1.549654412236324e13
0.10       -3.406049851783499e12
0.20       -6.800380653919192e11
0.30       -2.519643895319471e11
```

The sign survives the registered delta range, but the margin contracts sharply
as delta grows. In particular, the center-owner L2 charge cannot be reused for
delta `0.20` or `0.30` without a new owner-specific price.

Decision: `COVER-DELTA-SAMPLED-NEGATIVE`. This is not a uniform delta proof;
no full parameter quantifier or model-to-real transfer is closed. The next
viable coverage design is a delta-layered certificate with separately priced
L2/EM/matrix errors, followed by a far-delta argument.

Artifacts: `results/2082_cover_delta_margin_m6400.json` and
`results/2085_cover_delta03_m6400.json`.
Scripts: `scripts/routea_cover_delta_margin_m6400_2082.py` and
`scripts/routea_cover_delta03_single_2085.py`.