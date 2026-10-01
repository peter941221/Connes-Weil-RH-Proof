# 2358 - Directed nodal interval smoke

日期：2026-10-01。

## Result

The 2242 directed MPFR interval evaluator was reused on zero-width boxes for
the corrected 2303 owner at the binding strip node `sigma = -0.5`. With a
1001-point smoke grid it produced finite pointwise interval magnitudes and
the following trapezoidal readings:

```text
base_M0  = 2.6906382318515814
base_D2  = 8606.225861740026
corr_M0  = 90.7869637295159
corr_D2  = 125446.96411783129
```

The interval evaluator did not explode; the smoke min-product is
`337532.39772515034`. This supports pursuing the directed nodal-upper bridge
and rejects an immediate natural-interval no-go.

## Strict scope

This is not a nodal certificate. The grid is only 1001 points rather than the
committed 240001 points, the trapezoid remainder is not enclosed, and the
stored 2303 coordinate construction is not identified with this grid in a
Lean theorem. The smoke also does not import the result into the strip
consumer or the producer.

The next valid step is to run the same evaluator with the producer's full
node order and add a directed accumulation/remainder enclosure. No pin is
changed by this record.

Evidence: `scripts/routea_nodal_interval_smoke_2358.py` and
`results/2358_nodal_interval_smoke.json`.
