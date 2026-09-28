# 2062 - Route A C3' full-line tail survival probe

Date: 2026-09-28.

Status: TAIL-SURVIVES-MEASURED. This is a numerical narrowing result, not an
interval certificate, producer theorem, or RH claim.

Owner and consumer:

```text
owner = one-copy G8-H
support = 9.504
visible book = 1647 prime powers
consumer = C1P2DirectSemiLocalGate -> orbitWindowSemiLocalGate -> SourceRH
```

The first tail read at `m = 400` produced an apparent absolute tail of
`3.58e28` on `|xi| = 40..160`. Record 2053's evaluator-horizon law predicts
that this is alias pollution, not a mathematical tail. The `m = 1600` rerun
moved the cliff but still hit an alias regime on `120..160`.

The `m = 6400` rerun is the first usable survival screen for this window:

```text
absolute tail on 40..160 = 4.091205950971527e6
absolute tail / |Q1600| = 1.2011585575262929e-6
L2 charge / |Q1600|      = 1.295405449891678e-2
```

The measured tail is therefore four orders of magnitude below the L2 charge
and six orders below the sampled negative magnitude. The tail is not the
binding numerical component on this owner over the measured window.

Band readings:

```text
40..60    absolute = 3.4572049558493205e2
60..80    absolute = 3.6173763605805134e3
80..120   absolute = 2.0262609571879322e5
120..160  absolute = 3.8846167583965682e6
```

Decision: `TAIL-SURVIVES-MEASURED`.

Next exact obligation: prove an analytic or interval upper bound for
`|xi| > 160` on this same owner. The proof must carry the evaluator's own
trust horizon and cannot extrapolate the `m = 6400` measurement to infinity.

Nonclaims:

- no bound has yet been proved for `|xi| > 160`;
- no full-line quadrature enclosure has been proved;
- source-transform, kernel, and model-to-real enclosures remain open;
- no producer theorem or RH claim follows.

Reproducibility:

```text
python scripts/routea_c3p_tail_probe_2062.py
```

Artifacts:

- `results/2059_route_a_c3p_owner_margin.json`
- `results/2060_route_a_c3p_tail_probe.json` (m=400 alias incident)
- `results/2061_route_a_c3p_tail_probe.json` (m=1600 horizon incident)
- `results/2062_route_a_c3p_tail_probe.json` (m=6400 survival screen)
