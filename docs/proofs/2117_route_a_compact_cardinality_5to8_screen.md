# 2117 - Compact cardinality stress, five to eight added orbits

Date: 2026-09-28.

Status: `CARDINALITY-STRESS-SURVIVES-SCREENING`; not a producer theorem.

At `gamma=39.25244858548658`, `delta=0.445`, `scale=0.80`, the m=400
compact-ladder stress rows were:

```text
added orbits | nodes | support | prime book | condition       | Q (m=400)
5            | 50    | 5.056   | 49         | 1.019e8         | -3.8043e16
6            | 54    | 5.376   | 61         | 7.194e7         | -2.2677e16
7            | 58    | 5.696   | 79         | 5.004e8         | -2.0122e16
8            | 62    | 6.016   | 99         | 3.417e9         | -4.1503e16
```

The m=6400 rerun reproduced the first two signs before being stopped for
cost. This is a numerical stress screen only: the added points are not
asserted to be source zeros and the abstract owner remains
`sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes`.

The compact ladder remains the strongest selector candidate, but the rising
condition number and incomplete m=6400 run forbid a uniform-owner claim. The
next core gate is a proved cardinality bound for the actual closed-ball owner,
then owner-matched outward coefficient and signed-budget pricing.

Artifacts:

- `scripts/routea_owner_cardinality_compact_widths_5to8_m400_2117.py`
- `results/2117_owner_cardinality_compact_widths_5to8_m400.json`
- `scripts/routea_owner_cardinality_compact_widths_5to8_m6400_2118.py`

Nonclaims: no actual-owner completeness, no uniform conditioning theorem, no
outward certificate, no producer theorem, and no RH claim.
