# 2208 — NSEG=1100 vector-split binding refinement

Date: 2026-09-29

This is the next tightening step for the actual-owner Route-A matrix-action
enclosure. The two binding rows from 2206 were recomputed with `NSEG=1100` in
the endpoint-split Simpson interior.

```text
rhs          node   total bound       Simpson remainder
base          29    6.2349680e-08     6.2347025e-08
correction     2    4.9348932e-05     4.9346705e-05
```

The computed inner difference and endpoint terms remain negligible. Combining
the correction bound with the 2207 rounding allowance at the same scale gives
approximately `6.2e-5`; after the 2201 inverse norm this is about `7.4e-5`
relative coefficient movement, below the earlier `1e-4` screen.

Status: `VECTOR-SPLIT-BINDING-NSEG1100-PASS / FULL-MATRIX-UNPRICED`.

Only the two binding nodes were recomputed, and the allowance is not yet an
analytic outward interval. The full-node rule and transcendental enclosure
remain open. No producer theorem or RH claim follows.

