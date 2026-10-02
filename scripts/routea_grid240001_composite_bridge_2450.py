"""2450: composite bridge for the 240001-node directed full-grid re-run.

Combines the current repaired-evaluator 240001 span witnesses with the
2371 coordinate and panel prices, which were priced at exactly this grid
(nodes = 240001, sigma = -0.5, radius 6.553600000000003).  Interface
ledger only: no pointwise mathematical-term dominance, no Lean numeric
import, no producer GO.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FULLGRID = ROOT / "results/2450_fullgrid_240001_current.json"
PRICE = ROOT / "results/2371_coordinate_panel_price.json"
BRIDGE_776611 = ROOT / "results/2424_repaired_span_composite_bridge.json"

PIN_STRIP_GRID_MAX = 2644542.8515


def main() -> dict:
    grid = json.loads(FULLGRID.read_text())
    price = json.loads(PRICE.read_text())
    old_bridge = json.loads(BRIDGE_776611.read_text())

    if grid["nodes"] != 240001 or price["nodes"] != 240001:
        raise ValueError("both artifacts must be priced at 240001 nodes")
    if abs(grid["radius"] - price["radius"]) > 0:
        raise ValueError("radius mismatch between artifacts")

    span_rows = grid["directed_term_binary64_roundup_span_integrals"]
    parent = grid["directed_term_binary64_roundup_integrals"]
    price_rows = {row["channel"]: row for row in price["rows"]}
    old_rows = {row["channel"]: row for row in old_bridge["rows"]}
    order = ["base_M0", "base_D2", "corr_M0", "corr_D2"]

    rows = []
    for channel_index, (channel, parent_value) in enumerate(zip(order, parent)):
        span_value = sum(row[channel_index] for row in span_rows)
        pr = price_rows[channel]
        coordinate_charge = pr["coordinate_charge"]
        panel_remainder = pr["panel_remainder"]
        assembled = span_value + coordinate_charge + panel_remainder
        rows.append({
            "channel": channel,
            "span_sum_node_composite": span_value,
            "parent_roundup_node_composite": parent_value,
            "span_over_parent_ratio": span_value / parent_value,
            "coordinate_charge_2371": coordinate_charge,
            "panel_remainder_2371": panel_remainder,
            "assembled_upper_240001": assembled,
            "assembled_upper_776611": old_rows[channel]["assembled_upper"],
            "assembled_ratio_240001_over_776611":
                assembled / old_rows[channel]["assembled_upper"],
        })

    by_channel = {row["channel"]: row for row in rows}
    d2b_mc = by_channel["base_D2"]["assembled_upper_240001"] * \
        by_channel["corr_M0"]["assembled_upper_240001"]
    d2c_mb = by_channel["corr_D2"]["assembled_upper_240001"] * \
        by_channel["base_M0"]["assembled_upper_240001"]
    min_product = min(d2b_mc, d2c_mb)
    d2b_mc_old = by_channel["base_D2"]["assembled_upper_776611"] * \
        by_channel["corr_M0"]["assembled_upper_776611"]
    d2c_mb_old = by_channel["corr_D2"]["assembled_upper_776611"] * \
        by_channel["base_M0"]["assembled_upper_776611"]
    min_product_old = min(d2b_mc_old, d2c_mb_old)

    result = {
        "record": 2450,
        "status": "GRID240001_COMPOSITE_BRIDGE_INTERFACE_ONLY",
        "nodes": 240001,
        "sigma": grid["sigma"],
        "evaluator_source_sha256": grid["evaluator_source_sha256"],
        "grid_artifact_sha256": hashlib.sha256(FULLGRID.read_bytes()).hexdigest(),
        "price_artifact_sha256": hashlib.sha256(PRICE.read_bytes()).hexdigest(),
        "price_scope_note": (
            "2371 coordinate and panel prices were computed at exactly this "
            "grid; the curvature budget is operand-driven (2348 derivative "
            "ceilings) and is not moved by the evaluator repair margins"),
        "rows": rows,
        "min_product_channel_d2b_mc": d2b_mc,
        "min_product_channel_d2c_mb": d2c_mb,
        "assembled_min_product_240001": min_product,
        "assembled_min_product_776611": min_product_old,
        "pin_strip_grid_max_2311": PIN_STRIP_GRID_MAX,
        "min_product_over_pin": min_product / PIN_STRIP_GRID_MAX,
        "min_product_headroom_over_pin": PIN_STRIP_GRID_MAX / min_product,
        "headroom_776611_over_pin": PIN_STRIP_GRID_MAX / min_product_old,
        "lean_imported": False,
        "pointwise_mathematical_term_dominance_proved": False,
        "trapezoid_remainder_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    out = ROOT / "results/2450_grid240001_composite_bridge.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "status", "assembled_min_product_240001",
        "assembled_min_product_776611", "min_product_over_pin",
        "min_product_headroom_over_pin", "headroom_776611_over_pin")},
        indent=2))
    return result


if __name__ == "__main__":
    main()
