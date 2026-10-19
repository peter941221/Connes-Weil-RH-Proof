#!/usr/bin/env python3
"""Check that every exported 2804 charge covers the canonical interval jet."""
import hashlib
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
LEDGER = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"
OUT = ROOT / "results/3028_seed_ledger_canonical_charge_control.json"


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    canonical = load_module(ROOT / "scripts/seed_interval_jet_global_control_3027.py", "canonical3028")
    p3 = load_module(PARENT, "p3_3028")
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    mp.iv.dps = 40
    rows = ledger["rows"]
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / 8192
    max_ratio = {4: mp.mpf(0), 7: mp.mpf(0)}
    worst_excess = {4: (mp.mpf(0), -1), 7: (mp.mpf(0), -1)}
    checks = {4: True, 7: True}
    for i, row in enumerate(rows):
        left = lo + i * width
        right = lo + (i + 1) * width
        cell = mp.iv.mpf([left.a, right.b])
        jet = canonical.canonical_transition_jet(cell, 7)
        for order in (4, 7):
            canonical_charge = 4 * width * mp.iv.mpf([0, abs(jet[order]).b])
            canonical_upper = mp.mpf(canonical_charge.b)
            exported = mp.mpf(Fraction(row["charges"][str(order)]).numerator) / \
                Fraction(row["charges"][str(order)]).denominator
            checks[order] = checks[order] and canonical_upper <= exported
            excess = canonical_upper - exported
            if excess > worst_excess[order][0]:
                worst_excess[order] = (excess, i)
            if exported:
                max_ratio[order] = max(max_ratio[order], canonical_upper / exported)
    result = {
        "record": 3028,
        "status": "CONTROL-PASS" if all(checks.values()) else "CONTROL-FAIL",
        "cells": len(rows),
        "orders": [4, 7],
        "pointwise_charge_containment": {str(k): checks[k] for k in checks},
        "max_canonical_over_exported_ratio": {str(k): mp.nstr(max_ratio[k], 20) for k in max_ratio},
        "worst_canonical_minus_exported": {
            str(k): {"excess": mp.nstr(v[0], 30), "cell": v[1]}
            for k, v in worst_excess.items()
        },
        "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        "ledger_sha256": hashlib.sha256(LEDGER.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "nonclaims": [
            "Numerical interval control only.",
            "Does not prove mpmath evaluator-to-Lean endpoint soundness.",
            "Does not prove D4/D7, SourceRH, or RH."
        ],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
