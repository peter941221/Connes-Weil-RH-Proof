# 2070 - Explicit infinity-tail bound candidate

Date: 2026-09-28.

Status: INFINITY-TAIL-BOUND-CANDIDATE.

The fixed-r48 tail was extended from `1e6` to infinity with dyadic bands and
the interval archimedean kernel enclosure from record 2043. For the actual
one-copy G8-H owner:

```text
first band 1e6..2e6 log-bound = -2177.9202904243193
max observed dyadic ratio     = 8.168382914378888e-56
```

The band log-bound decreases by about `126.845` per doubling. The ordinary
float sum underflows to zero, which is favorable but not a meaningful printed
upper value; the log-bound is the authoritative reading.

The construction uses:

```text
fixed r = 48
N48 interval upper from 2068
explicit polynomial bound for P(xi)
fixed owner coefficient sums
2043 shifted-Stirling interval sigma enclosure
prime-book absolute majorant
```

Decision: the infinity tail is numerically eliminated by an explicit dyadic
algebraic envelope. Remaining audit work is to state the symbolic monotonicity
of the dyadic ratio and promote the 2068 variation skeleton to a proved N48
upper.

The next non-tail target is the finite-window signed quadrature on
`|xi| <= 40`, where the negative `Q1600` reading still needs an interval
certificate on the same owner.

Artifact: `results/2070_infinity_tail_bound.json`.
Script: `scripts/routea_infinity_tail_bound_2070.py`.
