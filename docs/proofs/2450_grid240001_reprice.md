# 2450 - Directed full-grid re-run at 240001 nodes and interface composite bridge

Date: 2026-10-02.

The directed full-grid certificate chain most recently ran at 776611 nodes.
The certified pin headroom at that grid (about 7x over `stripGridMax2303`)
is far above what the chain needs, and the coordinate and panel prices of
2371 were computed at exactly 240001 nodes. Running the node grid at
240001 removes the cross-grid mixing in the composite bridge: every input
then lives on one grid.

## What was run

The repaired evaluator (source hash `539ed1b4...`, the 2442-era repair that
restored directed rounding of the binary64 node values) was re-run over the
full strip grid at `nodes = 240001`, `sigma = -0.5`, twelve spans of 20001
nodes, sixteen workers.

    {"status": "DIRECTED_NODE_INTERVAL_FULL_GRID_SMOKE_NOT_CERTIFICATE",
     "nodes": 240001, "span": 20001,
     "interval_integrals": [2.6867143296475366, 8606.2144375546,
                            90.78788225389131, 125446.79342800482],
     "interval_min_product": 337039.697511355}

The twelve span witnesses reproduce the parent roundup integrals channel by
channel (`span_over_parent_ratio` is 1.0 up to one ulp on three channels and
1 + 2e-16 on the fourth).

## Composite bridge

The bridge script assembles, per channel, the 240001-node span sum plus the
2371 coordinate charge plus the 2371 panel remainder, and guards that both
source artifacts are priced at exactly 240001 nodes with equal radius.

    channel    assembled_upper_240001   assembled_upper_776611   ratio
    base_M0    2.7096814592279053       2.6889077598328956       1.0077
    base_D2    8713.463797039389        8616.457033939383        1.0113
    corr_M0    125.69320782730455       94.1214463847621         1.3354
    corr_D2    256800.2004410889        137991.35871664502       1.8610

The binding channel is `corr_D2 * base_M0` versus `base_D2 * corr_M0`;
the assembled min product and headroom against the pin are:

    assembled_min_product_240001   695846.7418612284   (0.2631x pin)
    assembled_min_product_776611   371046.03524307144  (0.1392x pin)
    headroom over stripGridMax2303 3.80x (240001)  7.13x (776611)

The direction of the change is the expected h^2-law price of the coarser
grid: the panel remainder grows roughly in proportion to the square of the
node spacing, and `corr_D2` carries the largest curvature, so its panel
term (131353.40 at this grid) dominates the per-channel growth. The span
sums themselves are unchanged; the min-product channel moves from
`corr_D2 * base_M0` at 776611 to the same channel at 240001 with 3.80x
headroom still held.

## Scope

Interface ledger only. The bridge adds artifact numbers that were priced on
the same grid; it does not prove pointwise mathematical-term dominance, does
not import the trapezoid remainder into Lean, and does not instantiate any
Lean constant. No signed selected-detector budget, producer GO or RH claim
follows.

Evidence:

- `scripts/routea_nodal_interval_fullgrid_2359.py` (evaluator, repaired source)
- `scripts/routea_grid240001_composite_bridge_2450.py`
- `results/2450_fullgrid_240001_current.json`
- `results/2450_grid240001_composite_bridge.json`
- `results/2371_coordinate_panel_price.json` (coordinate and panel prices, same grid)
- `results/2424_repaired_span_composite_bridge.json` (776611 comparison column)
