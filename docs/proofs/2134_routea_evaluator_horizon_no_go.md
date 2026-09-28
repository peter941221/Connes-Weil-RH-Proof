# 2134 — Route-A evaluator horizon closes the sampled full-line tail shortcut

Date: 2026-09-28.

Status: SCOPED-NO-GO-FOR-M6400-SAMPLED-TAIL-EXTRAPOLATION. This closes the
current quadrature extrapolation mechanism only. It does not close Route A,
the selected owner, or the analytic vertical-decay tail route.

Consumer and owner:

```text
one-copy G8-H selected-owner candidate
  -> aggregate signed kernel Q
  -> full-line tail certificate
  -> same-owner C3' gate
  -> SourceRH
```

The m=6400 evaluator was extended in three stages on the same owner
`rho = 0.6 + 40.9187190121475 i`, scale `0.88`, support `9.504`, and `1647`
visible prime powers. The measured tail ratios against
`|Q1600| = 3.406049871881275e12` were:

```text
range       tail absolute       tail / |Q1600|
40..160     4.09120595097e6      1.2011586e-6
160..240    8.52554759677e7      2.5030601e-5
240..400    1.28155240740e10     3.7625768e-3
400..600    4.83278978990e30     1.4188840e18
```

The jump occurs in the `500..550` band: its absolute reading is
`2.2280960477922288e30`. The `m=1600` control already showed the same
instrument failure earlier, with a `120..160` tail of approximately
`9.66e27`. Increasing m moves the cliff but does not turn the quadrature rule
into a full-line certificate.

Decision:

- Do not extrapolate the m=6400 sampled tail beyond its measured trust horizon.
- Do not use the `500..550` value as a mathematical tail estimate; it is the
  evaluator's alias regime.
- The next admissible tail target is an analytic vertical-decay bound, or an
  independently certified rule whose trust horizon is proved to exceed the
  required shell boundary.
- The finite-window signed margin remains a candidate only; no producer or RH
  theorem follows from these measurements.

Reproduce:

```text
python scripts/routea_c3p_tail_probe_2062.py
python scripts/routea_tail_horizon_extension_2132.py
python scripts/routea_tail_horizon_400_2133.py
python scripts/routea_tail_horizon_600_2134.py
```

Artifacts:

The authoritative extension artifacts are
  `results/2132_routea_tail_horizon_extension.json`,
  `results/2133_routea_tail_horizon_400.json`, and
  `results/2134_routea_tail_horizon_600.json`.
