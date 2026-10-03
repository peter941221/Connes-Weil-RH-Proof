"""2532: center-second-derivative plus third-derivative variation probe.

For each 2560-cell panel, bound the weighted second derivative by:

    |F''(mid)| + coefficient-error-charge(mid)
      + (cell_width / 2) * familywise_sup_sample(|F_i'''|).

The center second derivative preserves the 30-family signed cancellation. The
third derivative term is intentionally familywise and conservative. Its
supremum is sampled on a 17-point subgrid, so this remains a feasibility
probe, not a whole-cell certificate.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2532_signed_curvature_center_third_probe.json"
mp.mp.dps = 80


def q(text: str) -> mp.mpf:
    a, b = text.split("/") if "/" in text else (text, "1")
    return mp.mpf(a) / mp.mpf(b)


def load_families():
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        rlo = q(row["ideal_base_coefficient"]["real"]["lower_exact"])
        rhi = q(row["ideal_base_coefficient"]["real"]["upper_exact"])
        ilo = q(row["ideal_base_coefficient"]["imag"]["lower_exact"])
        ihi = q(row["ideal_base_coefficient"]["imag"]["upper_exact"])
        families.append(
            {
                "re": (rlo + rhi) / 2,
                "im": (ilo + ihi) / 2,
                "err": mp.sqrt(((rhi - rlo) / 2) ** 2 + ((ihi - ilo) / 2) ** 2),
                "radius": mp.mpf(float.fromhex(pair[0])) ** 2,
                "mod": mp.mpf(float.fromhex(pair[1])),
            }
        )
    return families


def derivative_terms(f, x: mp.mpf, sigma: mp.mpf):
    if abs(x) >= f["radius"]:
        return None
    r = f["radius"]
    u = x / r
    qv = 1 - u * u
    bump = mp.exp(-30 / qv)
    a1 = -60 * u / (r * qv**2)
    a2 = -60 * (1 + 3 * u * u) / (r**2 * qv**3)
    a3 = -720 * u * (1 + u * u) / (r**3 * qv**4)
    b1 = bump * a1
    b2 = bump * (a2 + a1 * a1)
    b3 = bump * (a3 + 3 * a1 * a2 + a1**3)
    lam = sigma + 1j * f["mod"]
    g2 = b2 + 2 * lam * b1 + lam**2 * bump
    g3 = b3 + 3 * lam * b2 + 3 * lam**2 * b1 + lam**3 * bump
    factor = mp.exp(sigma * x) * mp.exp(1j * f["mod"] * x)
    center2 = factor * g2
    center3_abs = (mp.sqrt(f["re"] ** 2 + f["im"] ** 2) + f["err"]) * mp.exp(sigma * x) * abs(g3)
    error2 = f["err"] * mp.exp(sigma * x) * abs(g2)
    return center2, center3_abs, error2


def run() -> dict:
    cells = 2560
    subnodes = 17
    radius = mp.mpf(65536001) / mp.mpf(10000000)
    step = 2 * radius / cells
    families = load_families()
    signs = {}
    node_sums = {"-0.5": mp.mpf("2.686887376406492"), "0.5": mp.mpf("2.675211462945179")}
    for sigma in (mp.mpf("-0.5"), mp.mpf("0.5")):
        remainder = mp.mpf(0)
        sampled_truth = mp.mpf(0)
        max_third = mp.mpf(0)
        max_location = None
        for index in range(cells):
            x0 = -radius + index * step
            x1 = x0 + step
            midpoint = (x0 + x1) / 2
            center = 0j
            error = mp.mpf(0)
            for family in families:
                term = derivative_terms(family, midpoint, sigma)
                if term is not None:
                    center += complex(family["re"], family["im"]) * complex(term[0])
                    error += term[2]
            third_sup = mp.mpf(0)
            for sub in range(subnodes):
                x = x0 + (x1 - x0) * sub / (subnodes - 1)
                third = sum(
                    (derivative_terms(family, x, sigma)[1]
                     if derivative_terms(family, x, sigma) is not None else 0)
                    for family in families
                )
                if third > third_sup:
                    third_sup = third
                    max_location = x
            bound = abs(center) + error + step / 2 * third_sup
            remainder += step**3 / 12 * bound
            max_third = max(max_third, third_sup)

            # Independent sampled truth comparison for the same cell.
            truth = mp.mpf(0)
            for sub in range(subnodes):
                x = x0 + (x1 - x0) * sub / (subnodes - 1)
                center_sample = 0j
                error_sample = mp.mpf(0)
                for family in families:
                    term = derivative_terms(family, x, sigma)
                    if term is not None:
                        center_sample += complex(family["re"], family["im"]) * complex(term[0])
                        error_sample += term[2]
                truth = max(truth, abs(center_sample) + error_sample)
            sampled_truth += step**3 / 12 * truth
        signs[str(sigma)] = {
            "curvature_remainder_center_third": mp.nstr(remainder, 60),
            "sampled_truth_remainder": mp.nstr(sampled_truth, 60),
            "ratio": mp.nstr(remainder / sampled_truth, 40),
            "max_familywise_third": mp.nstr(max_third, 60),
            "base_node_sum": mp.nstr(node_sums[str(sigma)], 60),
            "total_with_node": mp.nstr(remainder + node_sums[str(sigma)], 60),
            "base_endpoint_margin": mp.nstr(mp.mpf("2.7790943782") - remainder - node_sums[str(sigma)], 60),
        }
    return {
        "record": 2532,
        "status": "SIGNED_CURVATURE_CENTER_THIRD_FEASIBILITY_DIAGNOSTIC",
        "cells": cells,
        "subnodes": subnodes,
        "radius": str(radius),
        "step": str(step),
        "representation": "signed midpoint F'' plus coefficient error plus half-cell familywise F''' sample",
        "signs": signs,
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": ["sampled third-derivative supremum is not a certificate", "no Lean import", "no producer GO", "no SourceRH", "no RH"],
    }


def main() -> None:
    payload = run()
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()


