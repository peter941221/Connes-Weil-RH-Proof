"""Produce a decomposed, exact-rational replay certificate for one block."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_signed_jet_rect_arb_probe_3311 as probe

ROOT = Path(__file__).resolve().parents[1]


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--block", type=int, default=0)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 0 <= args.block < 160:
        raise SystemExit("block must be in [0, 160)")
    ctx.prec = args.precision

    endpoints = json.loads(
        (ROOT / "results/3300_routea_directed_cell_manifest.json").read_text(
            encoding="utf-8"
        )
    )["rows"][args.block * 256 : (args.block + 1) * 256]
    rows: list[dict[str, str | int]] = []
    component_sums = {name: F(0) for name in ("endpoint", "second", "fourth", "sixth")}
    step = F(endpoints[0]["step"])
    for offset, endpoint in enumerate(endpoints):
        index = args.block * 256 + offset
        second_family = [
            probe.exact_upper(rect.re_hi)
            for rect in probe.cell_family_rects(index, 2)
        ]
        fourth_family = [
            probe.exact_upper(rect.re_hi)
            for rect in probe.cell_family_rects(index, 4)
        ]
        second = sum(second_family, F(0))
        fourth = sum(fourth_family, F(0))
        endpoint_term = step * F(endpoint["value_upper"])
        second_term = step**3 * second / 24
        fourth_term = step**5 * fourth / 1920
        sixth_term = step**7 * F(endpoint["sixth_upper"]) / 322560
        component_sums["endpoint"] += endpoint_term
        component_sums["second"] += second_term
        component_sums["fourth"] += fourth_term
        component_sums["sixth"] += sixth_term
        rows.append(
            {
                "offset": offset,
                "index": index,
                "endpoint_upper": endpoint["value_upper"],
                "second_upper": str(second),
                "fourth_upper": str(fourth),
                "sixth_upper": endpoint["sixth_upper"],
                "second_family_upper": [str(value) for value in second_family],
                "fourth_family_upper": [str(value) for value in fourth_family],
                "endpoint_term": str(endpoint_term),
                "second_term": str(second_term),
                "fourth_term": str(fourth_term),
                "sixth_term": str(sixth_term),
            }
        )
    source = sum(component_sums.values(), F(0))
    target = F(
        json.loads(
            (ROOT / "results/3309_routea_corrected_signed_block_manifest.json").read_text(
                encoding="utf-8"
            )
        )["rows"][args.block]["block_upper"]
    )
    result = {
        "record": 3314,
        "status": "ARB_SIGNED_JET_DECOMPOSED_BLOCK_CERTIFICATE",
        "block": args.block,
        "cells": len(rows),
        "precision_bits": args.precision,
        "step": str(step),
        "component_sums": {name: str(value) for name, value in component_sums.items()},
        "source": str(source),
        "block_upper": str(ceil_grid(source)),
        "target_3309": str(target),
        "dominates_target_3309": source > target,
        "rows": rows,
        "arb_enclosure_proved": False,
        "lean_imported": False,
        "rh_claim": False,
    }
    output = args.output or ROOT / f"results/3314_block{args.block}_certificate.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("record", "block", "cells", "source", "block_upper", "target_3309")}, indent=2))


if __name__ == "__main__":
    main()
