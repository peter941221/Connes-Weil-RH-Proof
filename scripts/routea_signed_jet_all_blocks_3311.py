"""Parallel diagnostic block producer; no Lean enclosure is asserted."""

from __future__ import annotations

import argparse
import json
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_signed_jet_rect_arb_probe_3311 as probe

ROOT = Path(__file__).resolve().parents[1]


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def run_block(args: tuple[int, int]) -> dict:
    block, precision = args
    ctx.prec = precision
    endpoint = json.loads(
        (ROOT / "results/3300_routea_directed_cell_manifest.json").read_text()
    )["rows"][block * 256:(block + 1) * 256]
    target = F(
        json.loads(
            (ROOT / "results/3309_routea_corrected_signed_block_manifest.json").read_text()
        )["rows"][block]["block_upper"]
    )
    derivative_rows = {order: [] for order in (2, 4)}
    for order in derivative_rows:
        for index in range(block * 256, (block + 1) * 256):
            derivative_rows[order].append(
                probe.exact_upper(probe.cell_rect(index, order).re_hi)
            )
    step = F(endpoint[0]["step"])
    upper = F(0)
    for offset in range(256):
        upper += (
            step * F(endpoint[offset]["value_upper"])
            + step**3 * derivative_rows[2][offset] / 24
            + step**5 * derivative_rows[4][offset] / 1920
            + step**7 * F(endpoint[offset]["sixth_upper"]) / 322560
        )
    return {
        "block": block,
        "source": str(upper),
        "block_upper": str(ceil_grid(upper)),
        "target": str(target),
        "dominates_target": upper > target,
        "target_minus_upper": str(target - upper),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3311_all_blocks.json")
    args = parser.parse_args()
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(run_block, [(block, args.precision) for block in range(160)]))
    rows.sort(key=lambda row: row["block"])
    result = {
        "record": 3311,
        "status": "ARB_3310_RECTANGLE_ALL_BLOCK_COMPARISON",
        "blocks": 160,
        "workers": args.workers,
        "precision_bits": args.precision,
        "evaluator_revision": "3319_weight_pow60_arb_extrema_lean_grouping",
        "rows": rows,
        "failed_dominance_count": sum(row["dominates_target"] for row in rows),
        "upper_sum": str(sum((F(row["block_upper"]) for row in rows), F(0))),
        "target_sum": str(sum((F(row["target"]) for row in rows), F(0))),
        "lean_imported": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        key: result[key]
        for key in ("record", "status", "blocks", "workers", "failed_dominance_count", "upper_sum", "target_sum")
    }, indent=2))


if __name__ == "__main__":
    main()
