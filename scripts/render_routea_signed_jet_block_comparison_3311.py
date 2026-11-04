from __future__ import annotations

import json
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results/3311_block0_comparison.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteARationalSignedJetBlockComparison3311.lean"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--block", type=int, default=0)
    args = parser.parse_args()
    source = ROOT / f"results/3311_block{args.block}_comparison.json"
    output = ROOT / f"ConnesWeilRH/Dev/C1RouteARationalSignedJetBlock{args.block}Comparison3311.lean"
    payload = json.loads(source.read_text(encoding="utf-8"))
    rectangle = payload["rectangle_cell_upper_sum_ceil_1e-80"]
    target = payload["target_manifest_upper_ceil_1e-80"]
    text = f'''import ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309

namespace ConnesWeilRH.Dev

/-
Record 3311 block-0 arithmetic mirror.

The rectangle upper is generated from the finite rational operations mirrored
by `routea_signed_jet_rect_arb_probe_3311.py`, then rounded upward to 10^-80.
The external Arb computation is not imported as a theorem; this file proves
only the exact comparison of the recorded rational constants.
-/

def routeASignedJetRectBlock0Upper3311 : ℚ := {rectangle}

def routeACorrectedSignedBlock0Upper3309 : ℚ := {target}

theorem routeASignedJetRectBlock0Upper3311_le_manifest3309 :
    routeASignedJetRectBlock0Upper3311 ≤
      routeACorrectedSignedBlock0Upper3309 := by
  norm_num [routeASignedJetRectBlock0Upper3311,
    routeACorrectedSignedBlock0Upper3309]

end ConnesWeilRH.Dev
'''
    output.write_text(text.replace("Block0", f"Block{args.block}"), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
