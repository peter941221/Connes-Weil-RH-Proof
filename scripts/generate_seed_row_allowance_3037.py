#!/usr/bin/env python3
"""Export a conservative exact-rational allowance for every seed ledger row.

The 3029 replay bounds the largest observed excess by 6.7e-33.  The rational
allowance 1e-20 per row is intentionally much larger, while its 8192-row sum
is still negligible against both finite-target margins.  This artifact is an
input contract for the future Lean row proof; it does not claim evaluator
soundness by itself.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"
OUT = ROOT / "results/3037_seed_row_allowance.json"

def main():
    rows = json.loads(LEDGER.read_text(encoding="utf-8"))["rows"]
    assert len(rows) == 8192
    allowance = "1/100000000000000000000"
    payload = {
        "record": 3037,
        "status": "ROW-ALLOWANCE-EXPORTED",
        "cells": len(rows),
        "allowance_by_order": {"4": allowance, "7": allowance},
        "aggregate_by_order": {"4": "1024/12500000000000000000",
                                "7": "1024/12500000000000000000"},
        "rows": [{"index": r["index"], "allowance4": allowance,
                  "allowance7": allowance} for r in rows],
        "source_record": 3029,
        "nonclaims": [
            "This is an exact rational allowance budget only.",
            "It does not prove the evaluator-to-Lean row inequalities.",
            "It does not prove D4/D7, SourceRH, or RH."
        ],
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 3037, "status": payload["status"],
                      "cells": len(rows), "allowance": allowance,
                      "aggregate": payload["aggregate_by_order"]}, indent=2))

if __name__ == "__main__":
    main()
