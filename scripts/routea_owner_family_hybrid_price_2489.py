"""2489: price the Lean per-family hybrid curvature consumer.

This is a route-decision probe, not a certificate.  It evaluates exactly the
same production grid and the two sigma signs used by the Lean consumer, then
compares each family's endpoint-safe interval expression with its L1 baseline.
The output is intentionally labelled non-certified until a directed enclosure
and an independent anchor are attached.
"""
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2489_owner_family_hybrid_price.json"
mp.mp.dps = 80


def qfrac(text):
    p = text.split("/")
    return Fraction(int(p[0]), int(p[1])) if len(p) == 2 else Fraction(int(p[0]))


def mpq(value):
    return mp.mpf(value.numerator) / mp.mpf(value.denominator)


def l1_budget(order, coeff, mod, radius):
    total = mp.mpf("0")
    for j in range(order + 1):
        bump = (mp.mpf(1), mp.mpf(60), mp.mpf(3720))[order - j]
        total += (math.comb(order, j) * abs(mod) ** j * bump *
                  mp.exp(-30) / radius ** (order - j))
    return coeff * total


def curvature(sigma, radius, zero, first, second):
    return mp.exp(abs(sigma) * radius) * (
        second + 2 * abs(sigma) * first + sigma ** 2 * zero)


def interval_curvature(sigma, radius, t, coeff):
    scale = coeff * mp.exp(-30)
    first = scale * (60 * t / (1 - t * t) ** 2 / radius)
    second = scale * (60 * ((1 / (1 - t * t) ** 2) +
                            4 * t * t / (1 - t * t) ** 3) / radius ** 2 +
                      (60 * t / (1 - t * t) ** 2 / radius) ** 2)
    return curvature(sigma, radius, scale, first, second)


def main():
    cells = 640
    radius = mp.mpf(2076918743413931858457251756481) / mp.mpf(
        316912650057057350374175801344)
    step = 2 * radius / cells
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (qfrac(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              qfrac(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (qfrac(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              qfrac(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        coeff = mpq(abs(re) + abs(im))
        fam_radius = mp.mpf(float.fromhex(pair[0])) ** 2
        modulation = mp.mpf(float.fromhex(pair[1]))
        base = [l1_budget(k, coeff, modulation, fam_radius) for k in range(3)]
        families.append((fam_radius, modulation, coeff, curvature(
            mp.mpf("0.5"), fam_radius, *base)))

    rows = []
    for sigma in (mp.mpf("-0.5"), mp.mpf("0.5")):
        base_cells = []
        hybrid_cells = []
        safe_counts = []
        family_safe_total = 0
        for index in range(cells):
            left = -radius + index * step
            right = -radius + (index + 1) * step
            base_total = mp.mpf("0")
            hybrid_total = mp.mpf("0")
            safe_count = 0
            for fam_radius, modulation, coeff, _ in families:
                baseline = curvature(sigma, fam_radius,
                    l1_budget(0, coeff, modulation, fam_radius),
                    l1_budget(1, coeff, modulation, fam_radius),
                    l1_budget(2, coeff, modulation, fam_radius))
                base_total += baseline
                endpoint = max(abs(left), abs(right))
                if endpoint < fam_radius:
                    safe_count += 1
                    hybrid_total += min(
                        interval_curvature(
                            sigma, fam_radius, endpoint / fam_radius, coeff),
                        baseline)
                else:
                    hybrid_total += baseline
            family_safe_total += safe_count
            base_cells.append(base_total)
            hybrid_cells.append(hybrid_total)
            safe_counts.append(safe_count)
        base_remainder = sum(base_cells) * step ** 3 / 12
        hybrid_remainder = sum(hybrid_cells) * step ** 3 / 12
        rows.append({
            "sigma": float(sigma),
            "baseline_remainder": float(base_remainder),
            "hybrid_remainder": float(hybrid_remainder),
            "hybrid_to_baseline": float(hybrid_remainder / base_remainder),
            "baseline_max_cell": float(max(base_cells)),
            "hybrid_max_cell": float(max(hybrid_cells)),
            "safe_family_slots": family_safe_total,
            "safe_family_slots_total": cells * len(families),
            "safe_families_min_per_cell": min(safe_counts),
            "safe_families_max_per_cell": max(safe_counts),
        })
    result = {
        "record": 2489,
        "status": "HYBRID_PRICE_PROBE_NOT_A_CERTIFICATE",
        "grid": {"cells": cells, "step": float(step), "radius": float(radius)},
        "rows": rows,
        "decision": "price_same-grid_per-family_hybrid_before_directed_enclosure",
        "nonclaims": ["no Lean numeric certificate", "no producer GO", "no RH"],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
