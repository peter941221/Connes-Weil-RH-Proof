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
160..1e6 tail         8.096843616867657e-291
tail / |Q1600|       2.3771946746027827e-303
tail / L2 charge      1.8350970152252827e-301
```

The tail is therefore many orders below the existing finite-window L2 charge
on this numerical candidate. This does not certify the finite-window sign.

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
