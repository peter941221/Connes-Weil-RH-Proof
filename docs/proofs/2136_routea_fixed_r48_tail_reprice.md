# 2136 — Route-A fixed-r48 tail reprice after Lipschitz tightening

Date: 2026-09-28.

Status: FIXED-R48-TAIL-REPRICED-CANDIDATE. This is a same-owner numerical
repricing, not a producer theorem or an RH proof.

## Result

The fixed `r = 48` tail calculation from record 2069 was re-run with the
record-2135 variation upper bound, without changing the one-copy G8-H owner,
the `m = 6400` coefficient path, or the support/prime book.

```text
N48 upper             2.2934394233524673e73
positive 160..1e6 sampled integral  8.096843616867657e-291
positive / |Q1600|                  2.3771946746027827e-303
positive / L2 charge                1.8350970152252827e-301
```

These are positive-half-axis readings only, not a two-sided tail. The
`P_from_nodes` factor was evaluated as `abs(real(P))`, not its complex norm.
The geometric-grid trapezoid has no integral enclosure, its `1e6..infinity`
remainder is an unproved asymptotic model and underflows to zero in float.
Record 2137 audits both signs and the exact complex norm; cite its two-sided
reading instead. Neither record certifies the finite-window sign.

## Remaining boundary

```text
variation interval audit       open
infinity remainder proof       open
finite-window signed margin    open
actual closed-ball owner       open
```

Evidence:

```text
scripts/routea_fixed_r48_tail_price_2136.py
results/2136_routea_fixed_r48_tail_price.json
results/2135_routea_root_partition_lipschitz.json
results/2058_l5_solve.json
```

The artifact remains explicitly non-claiming because the owner is the
one-copy numerical G8-H candidate rather than the complete abstract
closed-ball healthy owner.
