from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results/3311_all_blocks.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteARationalSignedJetBlockManifest3312.lean"


def main() -> None:
    payload = json.loads(SOURCE.read_text(encoding="utf-8"))
    entries = ",\n    ".join(row["block_upper"] for row in payload["rows"])
    text = """import ConnesWeilRH.Dev.C1RouteARationalTightAggregate3299

namespace ConnesWeilRH.Dev

/-
Historical constants only. The generator omitted the 60th power in the 3310
weight and used unsafe comparisons of overlapping Arb balls. The sum theorem
below remains exact arithmetic, but these constants are not certified 3310
rectangle upper bounds and must not be treated as such.
-/

set_option linter.style.longLine false in
def routeASignedJetRectBlockUpper3312 : Fin 160 → ℚ := ![
    """ + entries + """
]

theorem routeASignedJetRectBlockUpper3312_sum_lt_zero :
    (∑ block : Fin 160, routeASignedJetRectBlockUpper3312 block) < 0 := by
  norm_num [Fin.sum_univ_succ, routeASignedJetRectBlockUpper3312]

theorem routeASignedJetRectBlockUpper3312_real_sum_lt_zero :
    (∑ block : Fin 160, (routeASignedJetRectBlockUpper3312 block : ℝ)) < 0 := by
  exact_mod_cast routeASignedJetRectBlockUpper3312_sum_lt_zero

end ConnesWeilRH.Dev
"""
    OUTPUT.write_text(text, encoding="utf-8")
    print(OUTPUT)


if __name__ == "__main__":
    main()
