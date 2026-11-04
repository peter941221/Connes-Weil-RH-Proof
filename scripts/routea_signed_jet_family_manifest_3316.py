"""Produce compact family-aggregated certificates for all 160 blocks."""

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
    endpoints = json.loads(
        (ROOT / "results/3300_routea_directed_cell_manifest.json").read_text(
            encoding="utf-8"
        )
    )["rows"][block * 256 : (block + 1) * 256]
    step = F(endpoints[0]["step"])
    second_family = [F(0) for _ in range(30)]
    fourth_family = [F(0) for _ in range(30)]
    endpoint_sum = F(0)
    sixth_sum = F(0)
    for offset, endpoint in enumerate(endpoints):
        index = block * 256 + offset
        endpoint_sum += step * F(endpoint["value_upper"])
        sixth_sum += step**7 * F(endpoint["sixth_upper"]) / 322560
        for family, rect in enumerate(probe.cell_family_rects(index, 2)):
            second_family[family] += probe.exact_upper(rect.re_hi)
        for family, rect in enumerate(probe.cell_family_rects(index, 4)):
            fourth_family[family] += probe.exact_upper(rect.re_hi)
    second_sum = step**3 * sum(second_family, F(0)) / 24
    fourth_sum = step**5 * sum(fourth_family, F(0)) / 1920
    source = endpoint_sum + second_sum + fourth_sum + sixth_sum
    old = json.loads(
        (ROOT / "results/3311_all_blocks.json").read_text(encoding="utf-8")
    )["rows"][block]
    return {
        "block": block,
        "step": str(step),
        "endpoint_sum": str(endpoint_sum),
        "second_family_sum": [str(value) for value in second_family],
        "fourth_family_sum": [str(value) for value in fourth_family],
        "sixth_sum": str(sixth_sum),
        "second_sum": str(second_sum),
        "fourth_sum": str(fourth_sum),
        "source": str(source),
        "block_upper": str(ceil_grid(source)),
        "previous_3311_block_upper": old["block_upper"],
        "arb_enclosure_proved": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3316_family_manifest.json")
    args = parser.parse_args()
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(run_block, [(block, args.precision) for block in range(160)]))
    rows.sort(key=lambda row: row["block"])
    result = {
        "record": 3316,
        "status": "ARB_SIGNED_JET_FAMILY_AGGREGATED_CERTIFICATE",
        "blocks": 160,
        "workers": args.workers,
        "precision_bits": args.precision,
        "rows": rows,
        "upper_sum": str(sum((F(row["block_upper"]) for row in rows), F(0))),
        "arb_enclosure_proved": False,
        "lean_imported": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("record", "status", "blocks", "upper_sum")}, indent=2))


if __name__ == "__main__":
    main()
