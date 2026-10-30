"""3181: diagnostic interpolation between existing base/correction boxes."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp

import routea_signed_finite_window_diagnostic_3179 as signed

ROOT = Path(__file__).resolve().parents[1]


def rational(text: str) -> mp.mpf:
    numerator, denominator = text.split("/") if "/" in text else (text, "1")
    return mp.mpf(numerator) / mp.mpf(denominator)


def load_families(alpha: mp.mpf) -> list[dict[str, mp.mpf]]:
    repair = json.loads(signed.base.REPAIR.read_text())
    capture = json.loads(signed.base.CAPTURE.read_text())["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        components = []
        for component in ("real", "imag"):
            base_box = row["ideal_base_coefficient"][component]
            corr_box = row["ideal_correction_coefficient"][component]
            base_mid = (rational(base_box["lower_exact"]) + rational(base_box["upper_exact"])) / 2
            corr_mid = (rational(corr_box["lower_exact"]) + rational(corr_box["upper_exact"])) / 2
            base_half = (rational(base_box["upper_exact"]) - rational(base_box["lower_exact"])) / 2
            corr_half = (rational(corr_box["upper_exact"]) - rational(corr_box["lower_exact"])) / 2
            components.append((base_mid + alpha * (corr_mid - base_mid), base_half + alpha * (corr_half - base_half)))
        families.append({
            "re": components[0][0],
            "im": components[1][0],
            "err": mp.sqrt(components[0][1] ** 2 + components[1][1] ** 2),
            "radius": mp.mpf(float.fromhex(pair[0])) ** 2,
            "mod": mp.mpf(float.fromhex(pair[1])),
        })
    return families


def integrate(families, radius: mp.mpf, cells: int, sigma: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    step = 2 * radius / cells
    midpoint = mp.mpf(0)
    charge = mp.mpf(0)
    for index in range(cells):
        x0 = -radius + index * step
        x1 = x0 + step
        c0, e0 = signed.signed_point_terms(families, x0, sigma)
        c1, e1 = signed.signed_point_terms(families, x1, sigma)
        midpoint += step / 2 * (c0 + c1)
        charge += step / 2 * (e0 + e1)
    return midpoint, charge


def run(cells: int, alpha_step: mp.mpf) -> dict:
    mp.mp.dps = 80
    radius = mp.mpf(65536001) / mp.mpf(10000000)
    rows = []
    steps = int(mp.floor(1 / alpha_step))
    for step_index in range(steps + 1):
        alpha = min(mp.mpf(1), step_index * alpha_step)
        families = load_families(alpha)
        signs = {}
        for sigma in (mp.mpf("-0.5"), mp.mpf("0.5")):
            midpoint, charge = integrate(families, radius, cells, sigma)
            signs[str(sigma)] = {
                "signed_midpoint_integral": mp.nstr(midpoint, 50),
                "coefficient_uncertainty_charge": mp.nstr(charge, 50),
                "signed_upper_diagnostic": mp.nstr(midpoint + charge, 50),
                "negative_midpoint": bool(midpoint < 0),
                "negative_upper": bool(midpoint + charge < 0),
            }
        rows.append({"alpha": mp.nstr(alpha, 30), "signs": signs})
    negatives = [row for row in rows if any(v["negative_midpoint"] for v in row["signs"].values())]
    return {
        "record": 3181,
        "status": "SIGNED_CORRECTION_INTERPOLATION_DIAGNOSTIC",
        "cells": cells,
        "alpha_step": mp.nstr(alpha_step, 30),
        "rows": rows,
        "negative_midpoint_count": len(negatives),
        "arithmetic": "mpmath 80 decimal digits; composite trapezoid; no curvature enclosure",
        "interpolation": "alpha=0 base midpoint/box, alpha=1 correction midpoint/box; intermediate alpha is diagnostic only",
        "owner_inputs": {
            "repair_sha256": hashlib.sha256(signed.base.REPAIR.read_bytes()).hexdigest(),
            "capture_sha256": hashlib.sha256(signed.base.CAPTURE.read_bytes()).hexdigest(),
        },
        "nonclaims": ["no certified quadrature error", "no Lean certificate", "no producer GO", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=640)
    parser.add_argument("--alpha-step", type=mp.mpf, default=mp.mpf("0.05"))
    parser.add_argument("--output", type=Path, default=ROOT / "results/3181_signed_correction_interpolation.json")
    args = parser.parse_args()
    result = run(args.cells, args.alpha_step)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "negative_midpoint_count": result["negative_midpoint_count"],
        "artifact": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
