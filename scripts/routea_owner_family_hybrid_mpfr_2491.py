"""2491: directed-MPFR price of the per-family hybrid curvature.

This is the next control after the 2489 high-precision price.  It reuses the
2478 directed MPFR bump enclosure, applies the same safe-cell split as the
Lean consumer, and takes the valid minimum of the directed interval family
upper and that family's L1 derivative-budget upper.  It remains external
data: no Lean literal import, producer GO, or RH claim is made here.
"""
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2491_owner_family_hybrid_mpfr.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2478", ROOT / "scripts/routea_owner_local_curvature_mpfr_2478.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
mpfr = base.mpfr


def exact_frac(text):
    parts = text.split("/")
    return Fraction(int(parts[0]), int(parts[1])) if len(parts) == 2 else Fraction(int(parts[0]))


def family_l1_curvature(sigma, radius, coefficient, modulation):
    constants = (1, 60, 3720)
    bounds = []
    for order in range(3):
        total = (0.0, 0.0)
        for j in range(order + 1):
            factor = math.comb(order, j) * abs(modulation) ** j
            bump = mpfr.mul(
                base.outward(factor * constants[order - j]),
                mpfr.div(base.outward(math.exp(-30)),
                         base.outward(radius ** (order - j))))
            total = mpfr.add(total, bump)
        bounds.append(mpfr.mul(coefficient, total))
    weight = mpfr.unary("mpfr_exp", mpfr.mul(base.outward(abs(sigma)),
                                               base.outward(radius)))
    weighted = mpfr.add(bounds[2], mpfr.add(
        mpfr.mul(base.outward(2 * abs(sigma)), bounds[1]),
        mpfr.mul(base.outward(sigma ** 2), bounds[0])))
    return mpfr.mul(weight, weighted)[1]


def directed_family_curvature(sigma, radius, modulation, coefficient,
                              left, right, step):
    bump = [base.bump_bound(order, radius, left, right, step)
            for order in range(3)]
    ext = []
    for order in range(3):
        value = (0.0, 0.0)
        for j in range(order + 1):
            term = mpfr.mul(
                base.outward(math.comb(order, j) * abs(modulation) ** j),
                bump[order - j][0])
            value = mpfr.add(value, term)
        ext.append(value)
    weighted = mpfr.add(ext[2], mpfr.add(
        mpfr.mul(base.outward(2 * abs(sigma)), ext[1]),
        mpfr.mul(base.outward(sigma ** 2), ext[0])))
    weight = mpfr.unary("mpfr_exp", mpfr.mul(base.outward(sigma),
                                               (base.outward(left)[0],
                                                base.outward(right)[1])))
    return mpfr.mul(coefficient, mpfr.mul(weight, weighted))[1]


def main():
    cells, subdiv = 40, 16
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (exact_frac(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              exact_frac(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (exact_frac(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              exact_frac(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        coefficient = base.exact_rational_interval(abs(re) + abs(im))
        families.append((float.fromhex(pair[0]) ** 2,
                         float.fromhex(pair[1]), coefficient))
    radius = 2076918743413931858457251756481 / 316912650057057350374175801344
    step = 2 * radius / cells
    substep = step / subdiv
    rows = []
    for sigma in (-0.5, 0.5):
        baseline_cells, hybrid_cells = [], []
        safe_slots = 0
        safe_counts = []
        for index in range(cells * subdiv):
            left = -radius + index * substep
            right = -radius + (index + 1) * substep
            baseline_total = (0.0, 0.0)
            hybrid_total = (0.0, 0.0)
            safe_count = 0
            for fam_radius, modulation, coefficient in families:
                baseline = family_l1_curvature(
                    sigma, fam_radius, coefficient, modulation)
                baseline_total = mpfr.add(baseline_total, (0.0, baseline))
                if max(abs(left), abs(right)) < fam_radius:
                    safe_count += 1
                    interval = directed_family_curvature(
                        sigma, fam_radius, modulation, coefficient,
                        left, right, substep)
                    chosen = min(interval, baseline)
                else:
                    chosen = baseline
                hybrid_total = mpfr.add(hybrid_total, (0.0, chosen))
            safe_slots += safe_count
            safe_counts.append(safe_count)
            baseline_cells.append(baseline_total[1])
            hybrid_cells.append(hybrid_total[1])
        exact_substep = Fraction.from_float(substep)
        factor = exact_substep ** 3 / 12
        baseline_remainder = factor * sum(
            (Fraction.from_float(value) for value in baseline_cells), Fraction(0))
        hybrid_remainder = factor * sum(
            (Fraction.from_float(value) for value in hybrid_cells), Fraction(0))
        rows.append({
            "sigma": sigma,
            "baseline_remainder": float(baseline_remainder),
            "hybrid_remainder": float(hybrid_remainder),
            "hybrid_to_baseline": float(hybrid_remainder / baseline_remainder),
            "baseline_max_cell": max(baseline_cells),
            "hybrid_max_cell": max(hybrid_cells),
            "safe_family_slots": safe_slots,
            "safe_family_slots_total": cells * subdiv * len(families),
            "safe_families_min_per_cell": min(safe_counts),
            "safe_families_max_per_cell": max(safe_counts),
        })
    result = {
        "record": 2491,
        "status": "DIRECTED_MPFR_HYBRID_PRICE_NOT_A_LEAN_CERTIFICATE",
        "backend": {"source": "2478 directed MPFR bump enclosure",
                    "rounding": "RNDD/RNDU"},
        "grid": {"cells": cells, "subdiv": subdiv,
                 "effective_cells": cells * subdiv, "step": substep},
        "rows": rows,
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "decision": "independent_directed_price_before_Lean_literal_import",
        "nonclaims": ["no Lean literal import", "no producer GO", "no RH"],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
