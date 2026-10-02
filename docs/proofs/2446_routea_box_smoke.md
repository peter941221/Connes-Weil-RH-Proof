# 2446 - Route A evaluator box smoke

Date: 2026-10-02.

The existing directed MPFR box evaluator from record 2242 was run through the
corrected-owner smoke driver on both strip endpoints. The measured minimum
products are:

```text
sigma     nodes    interval_min_product
-0.5      1001     337532.3977251508
-0.5      2001     337034.6206096492
 0.5      1001     268842.55655457673
```

The frozen producer constant is 9506275.102584327. The box smoke therefore
does not show an immediate interval-width explosion; the largest reading is
about 28.2 times below the frozen constant. The 2001-node reading also moves
down relative to 1001 nodes at sigma -0.5.

Evidence:

- results/2446_routea_box_smoke.json
- results/2446_routea_box_smoke_2001.json
- results/2446_routea_box_smoke_sigma_pos.json
- scripts/routea_nodal_interval_smoke_2358.py

This remains a smoke measurement. It does not prove the composite trapezoid
remainder, continuum strip transfer, Lean numeric import, signed detector
budget, producer GO, or RH.
