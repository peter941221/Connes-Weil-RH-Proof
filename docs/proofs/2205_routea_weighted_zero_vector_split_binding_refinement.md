# 2205 — Vector-aware split binding-node refinement

Date: 2026-09-29

Record 2204 priced the matrix action `A c` with vector-level cancellation but
used 100 Simpson half-panels per inner split. Its Simpson remainder was still
binding. Record 2205 recomputed the two binding rows with `NSEG=1000`.

## Results

```text
rhs          node   total bound       Simpson remainder
base          29    9.1284933e-08     9.1282280e-08
correction     2    7.2250740e-05     7.2248511e-05
```

The computed inner-difference and endpoint terms remain tiny; the displayed
bound is controlled by the explicit fourth-derivative Simpson remainder. With
the 2201 inverse norm, the corresponding provisional relative coefficient
movements are about `2.2e-4` for base and `8.6e-5` for correction. These are
still within the large direct-product budget headroom and the scale tested by
2199, but the all-node envelope has not yet been run.

## Status

Status: `VECTOR-SPLIT-BINDING-NODE-PASS / FULL-MATRIX-UNPRICED`.

This is not an outward certificate: only the two measured binding nodes were
refined, and floating quadrature/summation allowances remain uncharged. The
result keeps the matrix-level direct-product branch alive and sets the next
technical target: all 30 owner nodes at the refined rule, followed by an
analytic allowance for the computed matrix action. No producer theorem or RH
claim follows.

