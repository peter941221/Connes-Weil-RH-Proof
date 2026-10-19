#!/usr/bin/env python3
"""Price the canonical-vs-exported ledger rounding allowance."""
import importlib.util
import json
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
LEDGER = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"
BOUNDS = ROOT / "results/2730_seed_derivative_bounds.json"
OUT = ROOT / "results/3029_seed_ledger_rounding_allowance.json"


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    canonical = load(ROOT / "scripts/seed_interval_jet_global_control_3027.py", "canonical3029")
    # Load the same parent evaluator as the 2804 generator before setting
    # mpmath precision; its import-time context is part of the replay class.
    load(PARENT, "p3_3029")
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    bounds = json.loads(BOUNDS.read_text(encoding="utf-8"))
    mp.iv.dps = 40
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / 8192
    excess = {4: mp.mpf(0), 7: mp.mpf(0)}
    max_excess = {4: mp.mpf(0), 7: mp.mpf(0)}
    for i, row in enumerate(ledger["rows"]):
        cell = mp.iv.mpf([(lo + i * width).a, (lo + (i + 1) * width).b])
        jet = canonical.canonical_transition_jet(cell, 7)
        for order in (4, 7):
            canonical_charge = 4 * width * mp.iv.mpf([0, abs(jet[order]).b])
            canonical_upper = mp.mpf(canonical_charge.b)
            exported = mp.mpf(Fraction(row["charges"][str(order)]).numerator) / \
                Fraction(row["charges"][str(order)]).denominator
            delta = max(mp.mpf(0), canonical_upper - exported)
            excess[order] += delta
            max_excess[order] = max(max_excess[order], delta)
    getcontext().prec = 50
    margin = {}
    checks = {}
    for order, target in ((4, Decimal(1500)), (7, Decimal(2000000000))):
        bound_text = bounds["bounds"][str(order)]["upper_rational"]
        numerator, denominator = bound_text.split("/")
        bound = Decimal(numerator) / Decimal(denominator)
        allowance = Decimal(mp.nstr(excess[order], 50))
        margin[str(order)] = str(target - bound)
        checks[str(order)] = allowance < target - bound
    result = {
        "record": 3029,
        "status": "ALLOWANCE-PASS" if all(checks.values()) else "ALLOWANCE-FAIL",
        "cells": 8192,
        "total_excess": {str(k): mp.nstr(v, 30) for k, v in excess.items()},
        "max_cell_excess": {str(k): mp.nstr(v, 30) for k, v in max_excess.items()},
        "budget_margin": margin,
        "checks": checks,
        "nonclaims": [
            "Allowance pricing is numerical interval evidence.",
            "It does not prove evaluator-to-Lean endpoint soundness.",
            "It does not itself prove D4/D7, SourceRH, or RH."
        ],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
