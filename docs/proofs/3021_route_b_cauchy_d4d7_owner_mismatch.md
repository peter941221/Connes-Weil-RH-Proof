# 3021 Route B Cauchy/D4-D7 owner mismatch correction

The formal Cauchy chain added in records 3015--3018 proves a bound for the
function `routeBCenteredQ2900` and its Cauchy power-series tail.  The D4/D7
finite assembly in `routeB_finite_target_2812` instead integrates

```text
‖iteratedDeriv 4 Real.smoothTransition x‖
‖iteratedDeriv 7 Real.smoothTransition x‖
```

These are different mathematical owners.  Therefore the arithmetic bridge
recorded as `routeB_d4d7_cauchy_tail_bridge3019` is only a generic inequality
under explicit `finite4/finite7/tail4/tail7` premises; it does not establish
that the Cauchy tail is the tail of the D4/D7 integrals.

Decision:

```text
3015--3018: valid centered-Q Cauchy chain
3019: generic arithmetic only; not a semantic D4/D7 bridge
D4/D7 producer closure: still open
```

Any future D4/D7 tail theorem must identify the same Taylor owner, coefficient
normalization, and remainder object before it can consume a Cauchy bound.
