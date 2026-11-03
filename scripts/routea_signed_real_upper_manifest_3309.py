"""Build the 3309 outward-rounded manifest from the 3308 diagnostic rows.

The source values are Arb-derived rational upper enclosures. This script
rounds each value upward to a common decimal grid so the resulting constants
can be mirrored as exact Lean rationals without importing JSON into Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "results/3308_signed_real_upper_block_probe.json"
DEFAULT_OUTPUT = ROOT / "results/3309_routea_corrected_signed_block_manifest.json"
DEFAULT_LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteARationalCorrectedSignedBlockManifest3309.lean"
DECIMAL_SCALE = 10**80


def ceil_grid(value: F) -> F:
    """Return the least multiple of 10^-80 that is >= value."""
    numerator = value.numerator * DECIMAL_SCALE
    return F(-((-numerator) // value.denominator), DECIMAL_SCALE)


def lean_rat(value: F) -> str:
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def load_values(source: Path) -> tuple[dict, list[F]]:
    payload = json.loads(source.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list) or len(rows) != 160:
        raise ValueError("3308 source must contain exactly 160 rows")
    values: list[F] = []
    for expected_block, row in enumerate(rows):
        if int(row["block"]) != expected_block:
            raise ValueError(f"block index mismatch at row {expected_block}")
        values.append(F(row["signed_real_upper_block"]))
    return payload, values


def render_lean(values: list[F], source_name: str) -> str:
    entries = ",\n    ".join(lean_rat(value) for value in values)
    return f"""import ConnesWeilRH.Dev.C1RouteARationalTightAggregate3299

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-
Record 3309 arithmetic mirror.

These 160 rational constants are the 3308 corrected signed-real block
uppers rounded upward to the common 10^-80 grid. This module proves only
their exact arithmetic sum; it does not prove block dominance and it does
not import JSON as a theorem.

Source: {source_name}
-/

set_option linter.style.longLine false in
def routeACorrectedSignedBlockUpper3309 : Fin 160 → ℚ := ![
    {entries}]

theorem routeACorrectedSignedBlockUpper3309_sum_lt_zero :
    (∑ block : Fin 160, routeACorrectedSignedBlockUpper3309 block) < 0 := by
  norm_num [Fin.sum_univ_succ, routeACorrectedSignedBlockUpper3309]

theorem routeACorrectedSignedBlockUpper3309_real_sum_lt_zero :
    (∑ block : Fin 160, (routeACorrectedSignedBlockUpper3309 block : ℝ)) < 0 := by
  have h := routeACorrectedSignedBlockUpper3309_sum_lt_zero
  exact_mod_cast h

end ConnesWeilRH.Dev
"""


def build_manifest(source: Path) -> tuple[dict, str]:
    payload, source_values = load_values(source)
    rounded = [ceil_grid(value) for value in source_values]
    for index, (source_value, rounded_value) in enumerate(zip(source_values, rounded)):
        if rounded_value < source_value:
            raise AssertionError(f"rounding moved downward at block {index}")
        if rounded_value - source_value >= F(1, DECIMAL_SCALE):
            raise AssertionError(f"rounding slack too large at block {index}")

    total = sum(rounded, F(0))
    source_total = sum(source_values, F(0))
    if total >= 0:
        raise ValueError("outward-rounded block sum is not negative")

    rows = []
    for block, (source_value, rounded_value) in enumerate(zip(source_values, rounded)):
        rows.append({
            "block": block,
            "first_index": block * 256,
            "last_index": block * 256 + 255,
            "cell_count": 256,
            "source_signed_real_upper": str(source_value),
            "block_upper": str(rounded_value),
            "rounding_slack": str(rounded_value - source_value),
            "source_dominated": rounded_value >= source_value,
        })

    result = {
        "record": 3309,
        "status": "OUTWARD_ROUNDED_CORRECTED_SIGNED_BLOCK_MANIFEST",
        "source_record": int(payload["record"]),
        "source_file": str(source),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "cells": 40960,
        "block_size": 256,
        "block_count": 160,
        "rounding_grid": "1/10^80",
        "rounding_scale": DECIMAL_SCALE,
        "rows": rows,
        "block_upper_sum": str(total),
        "block_upper_sum_negative": total < 0,
        "source_sum": str(source_total),
        "source_sum_negative": source_total < 0,
        "max_rounding_slack": str(max(row["rounding_slack"] for row in rows)),
        "lean_certificate": False,
        "block_dominance_closed": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "The source is external Arb diagnostic evidence.",
            "The JSON manifest is not imported into Lean.",
            "The 160 block dominance inequalities remain separate premises.",
            "No producer_go, SourceRH, or RH claim is made.",
        ],
    }
    return result, render_lean(rounded, source.name)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--lean-output", type=Path, default=DEFAULT_LEAN)
    args = parser.parse_args()
    result, lean_text = build_manifest(args.source)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    args.lean_output.write_text(lean_text, encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "blocks": result["block_count"],
        "block_upper_sum": result["block_upper_sum"],
        "block_upper_sum_negative": result["block_upper_sum_negative"],
        "output": str(args.output),
        "lean_output": str(args.lean_output),
    }, indent=2))


if __name__ == "__main__":
    main()
