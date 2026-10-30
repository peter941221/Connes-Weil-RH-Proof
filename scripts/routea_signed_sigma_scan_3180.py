"""3180: diagnostic sigma scan for the current signed owner geometry."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp

import routea_signed_finite_window_diagnostic_3179 as base

ROOT = Path(__file__).resolve().parents[1]


def integrate(families, radius: mp.mpf, cells: int, sigma: mp.mpf) -> mp.mpf:
    step = 2 * radius / cells
    total = mp.mpf(0)
    for index in range(cells):
        x0 = -radius + index * step
        x1 = x0 + step
        c0, _ = base.signed_point_terms(families, x0, sigma)
        c1, _ = base.signed_point_terms(families, x1, sigma)
        total += step / 2 * (c0 + c1)
    return total


def run(cells: int, sigma_min: mp.mpf, sigma_max: mp.mpf, sigma_step: mp.mpf) -> dict:
    mp.mp.dps = 80
    families = base.base.load_families()
    radius = mp.mpf(65536001) / mp.mpf(10000000)
    values = []
    sigma = sigma_min
    while sigma <= sigma_max:
        midpoint = integrate(families, radius, cells, sigma)
        values.append({
            "sigma": mp.nstr(sigma, 30),
            "signed_midpoint_integral": mp.nstr(midpoint, 50),
            "negative": bool(midpoint < 0),
        })
        sigma += sigma_step
    minimum = min(values, key=lambda row: mp.mpf(row["signed_midpoint_integral"]))
    maximum = max(values, key=lambda row: mp.mpf(row["signed_midpoint_integral"]))
    return {
        "record": 3180,
        "status": "SIGNED_SIGMA_SCAN_DIAGNOSTIC",
        "cells": cells,
        "sigma_range": {
            "minimum": mp.nstr(sigma_min, 30),
            "maximum": mp.nstr(sigma_max, 30),
            "step": mp.nstr(sigma_step, 30),
        },
        "values": values,
        "minimum": minimum,
        "maximum": maximum,
        "negative_count": sum(row["negative"] for row in values),
        "arithmetic": "mpmath 80 decimal digits; composite trapezoid; no curvature enclosure",
        "owner_inputs": {
            "repair_sha256": hashlib.sha256(base.base.REPAIR.read_bytes()).hexdigest(),
            "capture_sha256": hashlib.sha256(base.base.CAPTURE.read_bytes()).hexdigest(),
        },
        "nonclaims": [
            "no certified quadrature error",
            "no owner repair",
            "no Lean certificate",
            "no producer GO",
            "no SourceRH",
            "no RH",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=640)
    parser.add_argument("--sigma-min", type=mp.mpf, default=mp.mpf("-1"))
    parser.add_argument("--sigma-max", type=mp.mpf, default=mp.mpf("1"))
    parser.add_argument("--sigma-step", type=mp.mpf, default=mp.mpf("0.1"))
    parser.add_argument("--output", type=Path, default=ROOT / "results/3180_signed_sigma_scan.json")
    args = parser.parse_args()
    result = run(args.cells, args.sigma_min, args.sigma_max, args.sigma_step)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "negative_count": result["negative_count"],
        "minimum": result["minimum"],
        "maximum": result["maximum"],
        "artifact": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
