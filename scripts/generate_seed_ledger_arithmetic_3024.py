#!/usr/bin/env python3
"""Generate the Lean exact-arithmetic projection of the 2804 ledger.

This proves row-count and aggregate arithmetic only.  It deliberately does
not claim that the Python interval evaluator is sound with respect to Lean's
derivative semantics; that bridge remains a separate theorem obligation.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteBSeedLedgerArithmetic3024.lean"


def write_list(handle, name, values):
    handle.write(f"def {name} : List ℚ := [\n")
    for offset in range(0, len(values), 32):
        chunk = values[offset : offset + 32]
        handle.write("  " + ",\n  ".join(chunk) + ",\n")
    handle.write("]\n\n")


def main():
    payload = json.loads(INPUT.read_text(encoding="utf-8"))
    rows = payload["rows"]
    if len(rows) != 8192 or [row["index"] for row in rows] != list(range(8192)):
        raise SystemExit("ledger row structure is not the expected 8192-row sequence")
    charge4 = [row["charges"]["4"] for row in rows]
    charge7 = [row["charges"]["7"] for row in rows]
    with OUTPUT.open("w", encoding="utf-8") as handle:
        handle.write("import Mathlib\n\nnamespace ConnesWeilRH.Dev\n\n")
        write_list(handle, "routeBSeedLedgerCharge4_3024", charge4)
        write_list(handle, "routeBSeedLedgerCharge7_3024", charge7)
        handle.write(
            "theorem routeBSeedLedgerCharge4_length3024 : "
            "routeBSeedLedgerCharge4_3024.length = 8192 := by norm_num\n"
        )
        handle.write(
            "theorem routeBSeedLedgerCharge7_length3024 : "
            "routeBSeedLedgerCharge7_3024.length = 8192 := by norm_num\n"
        )
        handle.write(
            "theorem routeBSeedLedgerCharge4_sum3024 : "
            f"routeBSeedLedgerCharge4_3024.sum = {payload['sums']['4']} := "
            "by norm_num [routeBSeedLedgerCharge4_3024]\n"
        )
        handle.write(
            "theorem routeBSeedLedgerCharge7_sum3024 : "
            f"routeBSeedLedgerCharge7_3024.sum = {payload['sums']['7']} := "
            "by norm_num [routeBSeedLedgerCharge7_3024]\n"
        )
        handle.write("\nend ConnesWeilRH.Dev\n")
    print(f"generated {OUTPUT} from {INPUT}")


if __name__ == "__main__":
    main()
