"""2533: signed grid-refinement curvature feasibility probe.

This record keeps the 2532 representation and exact owner fixed, but recomputes
both the signed center-plus-error node sum and the midpoint-second plus
familywise-third variation price on 2560, 5120, and 10240 cells.  The phase and
derivative ladder use the signed modulation; only the coefficient-radius
magnitude charge uses an absolute value.  The third-derivative supremum is
still sampled on a 17-point subgrid, so this is a routing diagnostic rather
than a whole-cell certificate.
"""
from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2533_signed_grid_refinement_probe.json"
mp.mp.dps = 70

BASE_PIN = mp.mpf("2.7790943782")
RADIUS = mp.mpf(65536001) / mp.mpf(10000000)


def q(text: str) -> mp.mpf:
    a, b = text.split("/") if "/" in text else (text, "1")
    return mp.mpf(a) / mp.mpf(b)


def mpf_fraction(value: mp.mpf) -> Fraction:
    sign, mantissa, exponent, _ = value._mpf_
    if mantissa == 0:
        return Fraction(0)
    result = Fraction(mantissa) * (Fraction(2) ** exponent)
    return -result if sign else result


def upward_binary_fraction(value: mp.mpf) -> Fraction:
    rounded = float(value)
    if not math.isfinite(rounded):
        raise ValueError("non-finite node payload")
    return Fraction.from_float(math.nextafter(rounded, math.inf))


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


def node_parts(families, x: mp.mpf, sigma: mp.mpf):
    center = mp.mpc(0)
    error = mp.mpf(0)
    for family in families:
        if abs(x) >= family["radius"]:
            continue
        u = x / family["radius"]
        qv = 1 - u * u
        bump = mp.exp(-30 / qv)
        phase = mp.exp(1j * family["mod"] * x)
        center += mp.mpc(family["re"], family["im"]) * bump * phase
        error += family["err"] * bump
    weight = mp.exp(sigma * x)
    return abs(center), error, weight, weight * (abs(center) + error)


def derivative_terms(family, x: mp.mpf, sigma: mp.mpf):
    if abs(x) >= family["radius"]:
        return None
    radius = family["radius"]
    u = x / radius
    qv = 1 - u * u
    bump = mp.exp(-30 / qv)
    a1 = -60 * u / (radius * qv**2)
    a2 = -60 * (1 + 3 * u * u) / (radius**2 * qv**3)
    a3 = -720 * u * (1 + u * u) / (radius**3 * qv**4)
    b1 = bump * a1
    b2 = bump * (a2 + a1 * a1)
    b3 = bump * (a3 + 3 * a1 * a2 + a1**3)
    # Keep the owner modulation signed in every phase and derivative term.
    lam = sigma + 1j * family["mod"]
    g2 = b2 + 2 * lam * b1 + lam**2 * bump
    g3 = b3 + 3 * lam * b2 + 3 * lam**2 * b1 + lam**3 * bump
    factor = mp.exp(sigma * x) * mp.exp(1j * family["mod"] * x)
    center2 = factor * g2
    coefficient_scale = mp.sqrt(family["re"] ** 2 + family["im"] ** 2) + family["err"]
    center3_abs = coefficient_scale * mp.exp(sigma * x) * abs(g3)
    error2 = family["err"] * mp.exp(sigma * x) * abs(g2)
    return center2, center3_abs, error2


def weighted_node_upper(families, x: mp.mpf, sigma: mp.mpf) -> mp.mpf:
    return node_parts(families, x, sigma)[3]


def run_grid(families, cells: int, sigma: mp.mpf, subnodes: int) -> dict:
    step = 2 * RADIUS / cells
    step_fraction = Fraction(131072002, 10000000 * cells)
    node_sum = mp.mpf(0)
    node_sum_upward = Fraction(0)
    for index in range(cells + 1):
        x_exact = Fraction(-65536001, 10000000) + index * step_fraction
        x = mp.mpf(x_exact.numerator) / mp.mpf(x_exact.denominator)
        upper = weighted_node_upper(families, x, sigma)
        if index < cells:
            x_next_exact = Fraction(-65536001, 10000000) + (index + 1) * step_fraction
            x_next = mp.mpf(x_next_exact.numerator) / mp.mpf(x_next_exact.denominator)
            upper_next = weighted_node_upper(families, x_next, sigma)
            node_sum += step / 2 * (upper + upper_next)
            node_sum_upward += step_fraction / 2 * (
                upward_binary_fraction(upper) + upward_binary_fraction(upper_next)
            )

    remainder = mp.mpf(0)
    sampled_truth = mp.mpf(0)
    max_third = mp.mpf(0)
    max_location = None
    for index in range(cells):
        x0 = -RADIUS + index * step
        x1 = x0 + step
        midpoint = (x0 + x1) / 2
        center = mp.mpc(0)
        error = mp.mpf(0)
        for family in families:
            term = derivative_terms(family, midpoint, sigma)
            if term is not None:
                center += mp.mpc(family["re"], family["im"]) * term[0]
                error += term[2]

        third_sup = mp.mpf(0)
        truth = mp.mpf(0)
        truth_location = None
        for sub in range(subnodes):
            x = x0 + (x1 - x0) * sub / (subnodes - 1)
            third = mp.mpf(0)
            center_sample = mp.mpc(0)
            error_sample = mp.mpf(0)
            for family in families:
                term = derivative_terms(family, x, sigma)
                if term is not None:
                    third += term[1]
                    center_sample += mp.mpc(family["re"], family["im"]) * term[0]
                    error_sample += term[2]
            if third > third_sup:
                third_sup = third
                truth_location = x
            sampled_value = abs(center_sample) + error_sample
            if sampled_value > truth:
                truth = sampled_value
        if third_sup > max_third:
            max_third = third_sup
            max_location = truth_location
        bound = abs(center) + error + step / 2 * third_sup
        remainder += step**3 / 12 * bound
        sampled_truth += step**3 / 12 * truth

    return {
        "cells": cells,
        "node_count": cells + 1,
        "step": mp.nstr(step, 60),
        "node_sum": mp.nstr(node_sum, 60),
        "node_sum_upward_binary_rational": f"{node_sum_upward.numerator}/{node_sum_upward.denominator}",
        "node_sum_upward_float": float(node_sum_upward),
        "curvature_remainder_center_third_sample": mp.nstr(remainder, 60),
        "sampled_truth_remainder": mp.nstr(sampled_truth, 60),
        "curvature_ratio": mp.nstr(remainder / sampled_truth, 40),
        "max_familywise_third": mp.nstr(max_third, 60),
        "max_familywise_third_location": mp.nstr(max_location, 40) if max_location is not None else None,
        "total_with_node": mp.nstr(node_sum + remainder, 60),
        "base_endpoint_margin": mp.nstr(BASE_PIN - node_sum - remainder, 60),
        "sampled_total_with_node": mp.nstr(node_sum + sampled_truth, 60),
    }


def main() -> None:
    families = load_families()
    grids = {}
    for cells in (2560, 5120, 10240):
        grids[str(cells)] = {}
        for sigma in (mp.mpf("-0.5"), mp.mpf("0.5")):
            grids[str(cells)][str(sigma)] = run_grid(families, cells, sigma, 17)

    payload = {
        "record": 2533,
        "status": "SIGNED_GRID_REFINEMENT_FEASIBILITY_DIAGNOSTIC",
        "representation": "signed center sum plus scalar coefficient error; midpoint F'' plus sampled familywise F''' variation",
        "cells": [2560, 5120, 10240],
        "subnodes": 17,
        "radius": str(RADIUS),
        "base_endpoint_pin": str(BASE_PIN),
        "modulation_policy": "signed modulation in phase and derivative lambda; absolute modulation only in magnitude envelopes",
        "grids": grids,
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": [
            "sampled third-derivative supremum is not a whole-cell certificate",
            "no Lean numeric payload import",
            "no exact midpoint-to-owner identity",
            "no selected-owner signed C3-prime margin",
            "no Producer GO",
            "no SourceRH",
            "no RH",
        ],
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    summary = {
        "record": payload["record"],
        "status": payload["status"],
        "base_endpoint_pin": str(BASE_PIN),
        "totals": {
            cells: {
                sigma: grids[cells][sigma]["total_with_node"]
                for sigma in ("-0.5", "0.5")
            }
            for cells in ("2560", "5120", "10240")
        },
        "margins": {
            cells: {
                sigma: grids[cells][sigma]["base_endpoint_margin"]
                for sigma in ("-0.5", "0.5")
            }
            for cells in ("2560", "5120", "10240")
        },
        "artifact": str(OUT),
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

