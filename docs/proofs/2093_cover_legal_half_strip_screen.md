# 2093 - Legal half-strip scale-0.86 COVER screen

Date: 2026-09-28.

Status: COVER-LEGAL-HALF-STRIP-CANDIDATE.

The formal source-zero interface proves `0 < Re(rho) < 1`, so on the positive
side the legal parameter range is `0 < delta < 0.5`. At the G8 height, fixed
scale `0.86` was rerun at `m=6400`:

```text
delta       Q(|xi|<=40)
0.10       -1.6038316410840713e13
0.30       -1.2910796022029832e12
0.50       -1.0171815682207738e12
```

The scale-0.86 owner therefore retains a large sampled margin at the legal
interior points and at the boundary stress point. This is substantially better
than scale `0.88` at delta `0.50`.

Decision: `COVER-LEGAL-HALF-STRIP-CANDIDATE`. The result still does not close
the gamma quantifier, the delta continuum, or the analytic/model-to-real
certificate. It narrows the next uniformity target to a legally bounded
half-strip with a plausible fixed scale, rather than the previously tested
unbounded delta pressure tests.

Artifact: `results/2093_cover_scale086_legal_delta_m6400.json`.
Script: `scripts/routea_cover_scale086_legal_delta_2093.py`.
Source strip evidence: `ConnesWeilRH/Source/CC20YoshidaNearZeros.lean:43` and
`:145`.