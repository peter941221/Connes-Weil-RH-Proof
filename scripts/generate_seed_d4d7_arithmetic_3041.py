#!/usr/bin/env python3
"""Generate Lean exact-arithmetic projection of the 3040 cell uppers."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results/3040_seed_d4d7_cell_upper.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteBSeedD4D7Arithmetic3041.lean"

def write_list(h, name, values):
    h.write(f"def {name} : List ℚ := [\n")
    for off in range(0, len(values), 32):
        h.write("  " + ",\n  ".join(values[off:off+32]) + ",\n")
    h.write("]\n\n")

def main():
    p = json.loads(INPUT.read_text(encoding="utf-8"))
    rows = p["rows"]
    assert len(rows) == 8192 and [r["index"] for r in rows] == list(range(8192))
    c4 = [r["4"] for r in rows]; c7 = [r["7"] for r in rows]
    with OUTPUT.open("w", encoding="utf-8") as h:
        h.write("import Mathlib\n\nnamespace ConnesWeilRH.Dev\n\n")
        write_list(h, "routeBSeedD4Upper3041", c4)
        write_list(h, "routeBSeedD7Upper3041", c7)
        h.write("theorem routeBSeedD4Upper_length3041 : routeBSeedD4Upper3041.length = 8192 := by norm_num\n")
        h.write("theorem routeBSeedD7Upper_length3041 : routeBSeedD7Upper3041.length = 8192 := by norm_num\n")
        h.write(f"theorem routeBSeedD4Upper_sum3041 : routeBSeedD4Upper3041.sum = {p['sums']['4']} := by norm_num [routeBSeedD4Upper3041]\n")
        h.write(f"theorem routeBSeedD7Upper_sum3041 : routeBSeedD7Upper3041.sum = {p['sums']['7']} := by norm_num [routeBSeedD7Upper3041]\n")
        h.write("\nend ConnesWeilRH.Dev\n")
    print(f"generated {OUTPUT}")

if __name__ == "__main__": main()
