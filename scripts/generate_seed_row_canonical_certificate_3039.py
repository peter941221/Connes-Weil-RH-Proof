#!/usr/bin/env python3
"""Export per-row canonical interval uppers against the exact ledger rows."""
import importlib.util, json
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"
OUT = ROOT / "results/3039_seed_row_canonical_certificate.json"

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def main():
    canonical = load(ROOT / "scripts/seed_interval_jet_global_control_3027.py", "canonical3039")
    load(ROOT / "scripts/p3_certified_strip_constants_2720.py", "p3_3039")
    rows = json.loads(LEDGER.read_text(encoding="utf-8"))["rows"]
    mp.iv.dps = 40
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / 8192
    allowance = Fraction(1, 10**20)
    out = []
    checks = {4: True, 7: True}
    for i, row in enumerate(rows):
        cell = mp.iv.mpf([(lo + i * width).a, (lo + (i + 1) * width).b])
        jet = canonical.canonical_transition_jet(cell, 7)
        item = {"index": i}
        for order in (4, 7):
            upper = mp.mpf((4 * width * mp.iv.mpf([0, abs(jet[order]).b])).b)
            exported = Fraction(row["charges"][str(order)])
            ok = upper <= mp.mpf(exported.numerator) / exported.denominator + mp.mpf(allowance.numerator) / allowance.denominator
            checks[order] = checks[order] and bool(ok)
            item[str(order)] = {"canonical_upper": mp.nstr(upper, 50),
                                "ledger": str(exported),
                                "allowance": str(allowance), "contains": bool(ok)}
        out.append(item)
    payload = {"record": 3039, "status": "ROW-CERTIFICATE-PASS" if all(checks.values()) else "ROW-CERTIFICATE-FAIL",
               "cells": len(out), "checks": {str(k): v for k, v in checks.items()},
               "rows": out, "nonclaims": ["mpmath interval evidence only", "not yet a Lean evaluator soundness proof"]}
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 3039, "status": payload["status"], "cells": len(out), "checks": payload["checks"]}, indent=2))

if __name__ == "__main__": main()
