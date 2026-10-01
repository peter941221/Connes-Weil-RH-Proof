# 2357 - Recomposition supersedes the overcharged 2339 budget

日期：2026-10-01。

## Direction correction

The 2356 replay correctly showed that the 2339 additive norm-transfer ledger
misses the frozen pin at `j=-50`. That failure is an overcharge diagnostic,
not evidence that the repaired owner itself exceeds the strip budget: 2339
adds the old full norm and the repair cost, thereby retaining the coefficient
inflation that the recomposed transfer must remove.

The existing 2340 recomposition is the valid next object. In the same WSL
Arb environment it replays with:

```text
all_nodes_fit_existing_pin = true
failed_nodes = []
maximum_node = -50
maximum_min_product_upper = 706456.176148581612...
existing_pin = 2644542.8515
old_inflation_reused = false
owner_transfer_to_live_consumer = false
```

The 2340 and 2341 selftests pass (9 and 11 tests respectively). The corrected
transfer therefore has ample numerical headroom, while remaining conditional
on the source-level nodal-upper theorem and coordinate identity. It has not
yet been imported into Lean or the live producer.

## Next binding obligation

The next proof object is not another pin increase. It is the directed nodal
upper bridge for the 2303 stored node evaluator, followed by the exact
coordinate-construction identity. Only after those two obligations are
closed may the 2340 upper be connected to the strip consumer and then to the
complete signed prime-power kernel.

No producer GO, detector sign transfer, map-103 reopening, or RH claim follows
from this correction.
