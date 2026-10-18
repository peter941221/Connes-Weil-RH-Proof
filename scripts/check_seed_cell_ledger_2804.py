#!/usr/bin/env python3
"""Exact structural and aggregate controls for the 2804 cell ledger."""
from fractions import Fraction
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"
PARENT = ROOT / "results/2730_seed_derivative_bounds.json"
OUT = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger_check.json"


def main():
    d = json.loads(LEDGER.read_text())
    p = json.loads(PARENT.read_text())
    rows = d["rows"]
    checks = {"row_count": len(rows) == 8192,
              "indices": [r["index"] for r in rows] == list(range(8192)),
              "nonnegative": all(Fraction(r["charges"][str(k)]) >= 0
                                  for r in rows for k in (4, 7)),
              "first_left": Fraction(rows[0]["left"]) == Fraction(1, 4096),
              "last_right": Fraction(rows[-1]["right"]) == Fraction(1, 2),
              "adjacent": all(Fraction(rows[i]["right"]) == Fraction(rows[i+1]["left"])
                              for i in range(len(rows) - 1))}
    for k in (4, 7):
        ledger_sum = Fraction(d["sums"][str(k)])
        parent_bound = Fraction(p["bounds"][str(k)]["upper_rational"])
        endpoint = Fraction(p["bounds"][str(k)]["endpoint_upper_rational"])
        # The parent interval accumulator has its own outward rounding; the
        # exported per-cell rationals must be below that aggregate, while the
        # analytic endpoint charge remains a separate nonnegative addend.
        checks[f"aggregate_{k}"] = ledger_sum <= parent_bound
        checks[f"endpoint_{k}"] = endpoint >= 0
    payload = {"record": 2804, "status": "CONTROL-PASS" if all(checks.values()) else "CONTROL-FAIL",
               "checks": checks, "nonclaims": [
                   "Does not prove evaluator-to-Lean soundness.",
                   "Does not prove finite integral, exterior tail, pins, SourceRH, or RH."]}
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
