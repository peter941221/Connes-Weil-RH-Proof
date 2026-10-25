#!/usr/bin/env python3
"""Test whether coarsening the existing transition jet clears D4/D7 targets.

This is a routing diagnostic. An excessive interval upper bound rejects that
certificate; it says nothing about a lower bound for the true integral.
"""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

import mpmath as mp

from diag_seed_rational_charge_3070 import endpoint_fraction, rational_transition_jet


def interval_of_fraction(value):
    return mp.iv.mpf(value.numerator) / value.denominator


def main():
    root = Path(__file__).resolve().parents[1]
    mp.mp.dps = 80
    mp.iv.dps = 80
    targets = {4: Fraction(1500), 7: Fraction(2000000000)}
    left = Fraction(1, 128)
    right = Fraction(1, 2)
    rows = []
    reference_controls = []
    for cells in (256, 512, 1024, 2048):
        width = (right - left) / cells
        totals = {k: mp.iv.mpf(0) for k in targets}
        for index in range(cells):
            a, b = left + index * width, left + (index + 1) * width
            ai, bi = interval_of_fraction(a), interval_of_fraction(b)
            cell = mp.iv.mpf([ai.a, bi.b])
            phase = 1 / (1 - cell) - 1 / cell
            scale = max(1, int(mp.ceil(-mp.mpf(phase.a))))
            jet = rational_transition_jet(cell, 7, scale)
            for order in targets:
                totals[order] += 4 * interval_of_fraction(width) * abs(jet[order])
            if index in (0, cells // 2, cells - 1):
                center_q = (a + b) / 2
                center = mp.mpf(center_q.numerator) / center_q.denominator

                def transition(x):
                    exponential = mp.exp(-1 / x + 1 / (1 - x))
                    return exponential / (1 + exponential)

                for order in targets:
                    reference = mp.diff(transition, center, order)
                    lo = endpoint_fraction(jet[order], False)
                    hi = endpoint_fraction(jet[order], True)
                    reference_controls.append(
                        mp.mpf(lo.numerator) / lo.denominator <= reference
                        <= mp.mpf(hi.numerator) / hi.denominator)
        readings = {}
        for order, target in targets.items():
            upper = endpoint_fraction(totals[order], True)
            readings[str(order)] = {
                "upper_rational": str(upper),
                "upper_decimal_diagnostic": mp.nstr(
                    mp.mpf(upper.numerator) / upper.denominator, 18),
                "target": str(target),
                "core_upper_below_full_target": upper < target,
            }
        rows.append({"cells": cells, "orders": readings})
    checks = {
        "partition_endpoints_exact": left + 2048 * ((right - left) / 2048) == right,
        "reference_controls": all(reference_controls),
        "reference_control_count": len(reference_controls) == 24,
        "all_tested_coarse_D4_uppers_exceed_target": all(
            not row["orders"]["4"]["core_upper_below_full_target"] for row in rows),
    }
    if not all(checks.values()):
        raise RuntimeError(f"probe controls failed: {checks}")
    sources = ["scripts/coarse_seed_enclosure_probe_3097.py",
               "scripts/diag_seed_rational_charge_3070.py"]
    report = {
        "record": 3097,
        "status": "COARSE_ENCLOSURES_DO_NOT_CLEAR",
        "owner": "Real.smoothTransition derivatives, rational-exp jet recurrence 2738",
        "interval": [str(left), str(right)],
        "iv_dps": mp.iv.dps,
        "rows": rows,
        "checks": checks,
        "provenance": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                       for name in sources},
        "nonclaims": [
            "No Lean numerical integral theorem or rounding certificate.",
            "An excessive upper enclosure is not a lower bound for the integral.",
            "No rejection of a finer grid, adaptive partition or different enclosure method.",
            "No row-B pins, universal-rho producer, Weil positivity or RH conclusion.",
        ],
    }
    (root / "results/3097_coarse_seed_enclosure_probe.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "checks": checks,
                      "rows": [{"cells": r["cells"],
                                "upper_diagnostics": {k: v["upper_decimal_diagnostic"]
                                                       for k, v in r["orders"].items()}}
                               for r in rows]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
