"""2277: cancellation-preserving corrected-owner numerical screen.

This is a decision probe, not a certificate. It evaluates the a^2 physical
profiles from the frozen 2249/2267 coefficient vectors before taking norms,
then compares a grid-refined screen with the rejected familywise majorant.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
PRICE = ROOT / "results/2276_owner_scale_price.json"
OUT = ROOT / "results/2277_corrected_cancellation_screen.json"
K = 30.0
SIGMAS = np.linspace(-0.5, 0.5, 101)

def load_owner():
    capture = json.loads(CAPTURE.read_text())
    owner = capture["owner_capture"]
    families = [(float.fromhex(width), float.fromhex(theta))
                for width, theta in owner["families_hex"]]
    base = np.array([complex(float.fromhex(real), float.fromhex(imag))
                     for real, imag in owner["base_hex"]])
    corr = np.array([complex(float.fromhex(real), float.fromhex(imag))
                     for real, imag in owner["corr_hex"]])
    return capture, families, base, corr

def fields(grid, families, coefficients):
    value = np.zeros(grid.shape, dtype=complex)
    second = np.zeros(grid.shape, dtype=complex)
    third = np.zeros(grid.shape, dtype=complex)
    for coefficient, (width, theta) in zip(coefficients, families):
        radius = width * width
        u = grid / radius
        q = 1.0 - u * u
        mask = q > 0.0
        phi = np.zeros_like(grid)
        phi[mask] = np.exp(-K / q[mask])
        first_log = np.zeros_like(grid)
        first_log[mask] = -2.0 * K * u[mask] / (radius * q[mask] ** 2)
        second_log = np.zeros_like(grid)
        second_log[mask] = (-2.0 * K / radius ** 2 *
                            (q[mask] ** -2 + 4.0 * u[mask] ** 2 * q[mask] ** -3))
        third_log = np.zeros_like(grid)
        third_log[mask] = (-24.0 * K * u[mask] / radius ** 3 * q[mask] ** -3
                           - 48.0 * K * u[mask] ** 3 / radius ** 3 * q[mask] ** -4)
        phase = np.exp(1j * theta * grid)
        term = coefficient * phi * phase
        value += term
        second += term * (second_log + first_log ** 2
                          + 2j * theta * first_log - theta ** 2)
        third += term * (
            third_log + 3.0 * first_log * second_log + first_log ** 3
            + 3j * theta * (second_log + first_log ** 2)
            - 3.0 * theta ** 2 * first_log
            - 1j * theta ** 3
        )
    return value, second, third

def norm_rows(grid, families, base, corr):
    base0, base2, base3 = fields(grid, families, base)
    corr0, corr2, corr3 = fields(grid, families, corr)
    rows = []
    for sigma in SIGMAS:
        weight = np.exp(sigma * grid)
        mb = float(np.trapezoid(np.abs(base0) * weight, grid))
        db = float(np.trapezoid(np.abs(base2) * weight, grid))
        b3 = float(np.trapezoid(np.abs(base3) * weight, grid))
        mc = float(np.trapezoid(np.abs(corr0) * weight, grid))
        dc = float(np.trapezoid(np.abs(corr2) * weight, grid))
        c3 = float(np.trapezoid(np.abs(corr3) * weight, grid))
        rows.append({"sigma": float(sigma), "base_M0": mb, "base_D2": db,
                     "base_D3": b3, "corr_M0": mc, "corr_D2": dc,
                     "corr_D3": c3, "C_upper": min(db * mc, dc * mb) / (2 * math.pi) ** 2})
    return rows

def summarize(rows):
    best = max(rows, key=lambda row: row["C_upper"])
    return {"best": best, "B_upper": (2 * math.pi) ** 2 * best["C_upper"],
            "rows": rows}

def conservative_tail_from_row(row):
    factor = (9.0 ** 8 / 6.0 ** 12) * 2.0 * (
        (8.0 + 28056.0) / (3.0 * 40.0 ** 3) + 1152.0 / 40.0)
    return factor * row["base_D3"] ** 2 * row["corr_D3"] ** 2

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=120001)
    parser.add_argument("--refine", action="store_true")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    capture, families, base, corr = load_owner()
    max_radius = max(width * width for width, _ in families)
    grid = np.linspace(-max_radius, max_radius, args.nodes)
    coarse = summarize(norm_rows(grid, families, base, corr))
    result = {"record": 2277, "status": "CANCELLATION-PRESERVING-SCREEN",
              "certificate": False, "hgap_closed": False,
              "grid": {"nodes": args.nodes, "half_width": max_radius,
                       "step": float(grid[1] - grid[0])},
              "owner": {"physical_profile": "phi_(a^2)(y)",
                        "families": len(families),
                        "base_md5": capture["owner_capture"]["base_md5"],
                        "corr_md5": capture["owner_capture"]["corr_md5"]},
              "screen": coarse,
              "conservative_tail_screen": conservative_tail_from_row(coarse["best"]),
              "rejected_familywise": json.loads(PRICE.read_text())["norm_upper_expression_enclosures"],
              "nonclaims": ["sampled trapezoids are not analytic enclosures",
                            "no selected-detector readback",
                            "no hstrip or hgap supplier",
                            "no producer GO or RH claim"],
              "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in (CAPTURE, PRICE)}}
    if args.refine:
        fine_grid = np.linspace(-max_radius, max_radius, 240001)
        fine = summarize(norm_rows(fine_grid, families, base, corr))
        result["refinement"] = {
            "coarse_nodes": args.nodes, "fine_nodes": 240001,
            "coarse_B": coarse["B_upper"], "fine_B": fine["B_upper"],
            "relative_B_change": abs(fine["B_upper"] - coarse["B_upper"]) / max(abs(fine["B_upper"]), 1.0),
            "coarse_best": coarse["best"], "fine_best": fine["best"]}
        result["refinement"]["coarse_tail"] = conservative_tail_from_row(coarse["best"])
        result["refinement"]["fine_tail"] = conservative_tail_from_row(fine["best"])
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("CANCELLATION-PRESERVING-SCREEN")
    print(json.dumps({"B_upper": coarse["B_upper"], "best_sigma": coarse["best"]["sigma"]}))

if __name__ == "__main__":
    main()
