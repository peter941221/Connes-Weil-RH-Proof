# 2524 - 640-cell actual-owner node-sum diagnostic

Date: 2026-10-03.

The 640-cell replay of the exact-owner node formula used by
`ownerPanelNodeUpper2471` gives the following composite node prices:

```text
sigma = -1/2      89.1680855402758020651089637146469...
sigma = +1/2      89.1686519152896939566135685512794...
```

The same formula at the earlier ten-cell diagnostic was about `8279`, so the
production grid removes the coarse-panel inflation. This is a feasibility
signal for the next certificate step.

The run uses the exact rational coefficient-ball endpoints from record 2338,
the exact stored owner radii and modulations, and the 2471 half-step panel
geometry. It keeps the 30-family sum composed before taking the rectangle norm.

This record is diagnostic only. The evaluator uses high-precision
transcendental values but does not yet provide a directed MPFR endpoint ledger
or a Lean literal import. It therefore does not close `compositeNodeUpper2347`,
the strip certificate, the signed C3' budget, producer GO, or RH.

Evidence:

- `scripts/routea_owner_panel_node_price_2524.py`
- `results/2524_owner_panel_node_price.json`
- `docs/proofs/2471_owner_panel_node_upper.md`
