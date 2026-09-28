# 2120 - Nearby zero-free Jensen anchor screen

Date: 2026-09-28.

Status: `ANCHOR-IMPROVES-BUT-NOT-GO`.

Record 2119 used the fixed Jensen center `2`. The formal module now also
proves `sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth_at_center`,
which allows any nonzero center. For a hypothetical owner at
`rho=0.945+39.25244858548658i`, centers on the zero-free line `Re(c) >= 1`
were screened numerically.

```text
Re(c) | center distance | Jensen radius | rung n | owner bound
1.0   | 0.055           | 43.322        | 3      | 1370.790
1.2   | 0.255           | 43.522        | 3      | 1370.651
1.4   | 0.455           | 43.722        | 3      | 1370.477
1.5   | 0.555           | 43.822        | 3      | 1370.380
```

The nearby anchor reduces the fixed-center translation from about `3002.56`
to about `1370.38`, but the best screened bound is still about `22.1x` the
62-node compact family. This is a real improvement in the formal interface,
not a Go: it still does not certify that the actual owner has only 62 nodes.

The xi values in the table are numerical translations of the exact Lean
expression and are not Lean numeral certificates. No measured zero count,
producer theorem, or RH claim is made.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean`
- `results/2120_routea_nearby_anchor_cardinality_screen.json`
- `scripts/routea_nearby_anchor_cardinality_screen_2120.py`
- audit: `build-logs/routea_owner_cardinality_audit_20260928_v5.log`

Next core move: replace the broad xi-growth/Jensen envelope with a sharper
explicit zero-count certificate on this bounded height window, or abandon
one-node-per-owner-zero interpolation in favor of an owner-local signed
construction.
