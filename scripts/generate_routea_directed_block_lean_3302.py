"""Generate the 3302 Lean arithmetic mirror for directed block bounds."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def lean_rat(value: F) -> str:
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "results/3300_routea_directed_cell_manifest.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "ConnesWeilRH/Dev/C1RouteARationalTightBlockManifest3302.lean",
    )
    args = parser.parse_args()
    payload = json.loads(args.manifest.read_text(encoding="utf-8"))
    blocks = payload["blocks"]
    if len(blocks) != 160:
        raise ValueError("expected exactly 160 blocks")

    values = [F(block["cell_upper_exact_fraction"]) for block in blocks]
    if sum(values, F(0)) >= 0:
        raise ValueError("directed block sum is not negative")

    entries = ",\n    ".join(lean_rat(value) for value in values)
    text = f"""import ConnesWeilRH.Dev.C1RouteARationalTightAggregate3299

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-
Record 3302 arithmetic mirror.

These 160 rational constants are generated from the external directed-rounding
3301 block manifest. This module proves only the arithmetic fact that their
sum is negative. It does not prove that the constants dominate
ratCellValueUpperTight3298, and it does not import JSON as endpoint evidence.
-/

set_option linter.style.longLine false in
def routeADirectedBlockUpper3302 : Fin 160 → ℚ := ![
    {entries}]

theorem routeADirectedBlockUpper3302_sum_lt_zero :
    (∑ block : Fin 160, routeADirectedBlockUpper3302 block) < 0 := by
  norm_num [Fin.sum_univ_succ, routeADirectedBlockUpper3302]

theorem routeADirectedBlockUpper3302_real_sum_lt_zero :
    (∑ block : Fin 160, (routeADirectedBlockUpper3302 block : ℝ)) < 0 := by
  have h := routeADirectedBlockUpper3302_sum_lt_zero
  exact_mod_cast h

end ConnesWeilRH.Dev
"""
    args.output.write_text(text, encoding="utf-8")
    print(json.dumps({
        "record": 3302,
        "status": "GENERATED_LEAN_BLOCK_ARITHMETIC_MIRROR",
        "blocks": len(blocks),
        "sum_negative": sum(values, F(0)) < 0,
        "output": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
