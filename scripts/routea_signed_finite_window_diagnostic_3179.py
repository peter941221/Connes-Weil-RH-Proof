"""3179: diagnostic signed finite-window screen for the current owner."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp

import routea_owner_signed_cancellation_2528 as base

ROOT = Path(__file__).resolve().parents[1]


def signed_point_terms(families, x, sigma):
    center = mp.mpc(0)
    error = mp.mpf(0)
    for family in families:
        terms = base.bump_terms(family, x)
        if terms is None:
            continue
        bump, _, _ = terms
        phase = mp.exp(1j * family["mod"] * x)
        center += mp.mpc(family["re"], family["im"]) * bump * phase
        error += family["err"] * bump
    weight = mp.exp(sigma * x)
    return weight * center.real, weight * error


def run(cells: int) -> dict:
    mp.mp.dps = 100
    families = base.load_families()
    radius = mp.mpf(65536001) / mp.mpf(10000000)
    step = 2 * radius / cells
    result = {"record": 3179, "status": "SIGNED_FINITE_WINDOW_DIAGNOSTIC", "cells": cells, "signs": {}}
    for sigma in (mp.mpf("-0.5"), mp.mpf("0.5")):
        signed_center = mp.mpf(0)
        error_charge = mp.mpf(0)
        for index in range(cells):
            x0 = -radius + index * step
            x1 = x0 + step
            c0, e0 = signed_point_terms(families, x0, sigma)
            c1, e1 = signed_point_terms(families, x1, sigma)
            signed_center += step / 2 * (c0 + c1)
            error_charge += step / 2 * (e0 + e1)
        upper = signed_center + error_charge
        result["signs"][str(sigma)] = {
            "signed_midpoint_integral": mp.nstr(signed_center, 60),
            "coefficient_uncertainty_charge": mp.nstr(error_charge, 60),
            "signed_upper_diagnostic": mp.nstr(upper, 60),
            "negative_midpoint": bool(signed_center < 0),
            "negative_upper": bool(upper < 0),
        }
    result.update({
        "coefficient_representation": "2338 box midpoint plus Euclidean radius charge",
        "arithmetic": "mpmath 100 decimal digits; composite trapezoid; no curvature enclosure",
        "owner_inputs": {
            "repair_sha256": hashlib.sha256(base.REPAIR.read_bytes()).hexdigest(),
            "capture_sha256": hashlib.sha256(base.CAPTURE.read_bytes()).hexdigest(),
        },
        "nonclaims": ["no certified quadrature error", "no Lean certificate", "no producer GO", "no SourceRH", "no RH"],
    })
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3179_signed_finite_window_diagnostic.json")
    args = parser.parse_args()
    result = run(args.cells)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
