# 2135 — Route-A root-partition Lipschitz tightening

Date: 2026-09-28.

Status: ROOT-PARTITION-LIPSCHITZ-CANDIDATE. This materially tightens the
fixed-order tail enclosure, but it is not yet a producer theorem or an RH
proof.

## Consumer and obligation

```text
same-owner finite-window signed margin
    -> |xi| > 160 tail bound
    -> same-owner C3' gate
    -> SourceRH
```

The calculation addresses only the high-order variation constant used by the
tail bound. It does not change the owner, visible-prime set, selector, or
quantifier order.

## Method

Record 2066 supplies 64 exact rational isolating intervals for the real roots
of the order-48 derivative numerator on `(-1, 1)`. On every root interval
`[l, r]`:

```text
mid = (l + r) / 2
value = phi^(47)(mid)
error <= sup_[l,r] |phi^(48)| * (r - l) / 2
```

The interval values of `phi^(47)` are then assembled across the monotonicity
partition, with zero endpoint values at `u = -1` and `u = 1`.

This avoids the severe dependency inflation from evaluating the full
`phi^(47)` expression directly over each root interval.

## Result

```text
root count                         64
max root interval width            8.208978016844e-41
max Lipschitz error                1.1876536686546546e18
variation upper                    2.2934394233524675e73
measured N48                       2.2934374717100001e73
upper / measured                   1.0000008509682481
improvement over record 2068       5.435680472e7
```

Evidence:

```text
scripts/routea_root_partition_lipschitz_2135.py
results/2135_routea_root_partition_lipschitz.json
results/2066_exact_root_isolation.json
results/2068_interval_variation_bound.json
```

## Boundary

The result remains a candidate because the following gates are not yet
independent formal facts:

1. mpmath interval rounding must be cross-checked by Arb or an exact rational
   enclosure.
2. Root completeness and the endpoint-to-monotonicity bridge must be audited
   independently.
3. The coefficient path and actual selected-owner transfer are still open.

The owner in this record is the one-copy numerical G8-H candidate. Therefore
this result cannot be promoted to the actual closed-ball healthy-owner
producer without a separate owner-transfer certificate.
