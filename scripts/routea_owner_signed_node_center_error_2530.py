"""2530: diagnostic center-plus-scalar-error node payload.

Generate per-node payloads for the viable 2528 representation.  The center
30-family complex sum is retained until the modulus; the coefficient-box
uncertainty is a separate scalar charge.  Each weighted upper is exported as
an upward-rounded binary64 rational for a later Lean import attempt.

This artifact is still diagnostic: phase/bump transcendental evaluations have
not yet received Lean-side directed enclosures, and the curvature payload is
not generated here.
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
OUT = ROOT / "results/2530_signed_node_center_error_payload.json"
mp.mp.dps = 100


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
    for f in families:
        if abs(x) >= f["radius"]:
            continue
        u = x / f["radius"]
        qv = 1 - u * u
        bump = mp.exp(-30 / qv)
        phase = mp.exp(1j * f["mod"] * x)
        center += mp.mpc(f["re"], f["im"]) * bump * phase
        error += f["err"] * bump
    weight = mp.exp(sigma * x)
    center_norm = abs(center)
    weighted_upper = weight * (center_norm + error)
    return center_norm, error, weight, weighted_upper


def main() -> None:
    cells = 2560
    radius = mp.mpf(65536001) / mp.mpf(10000000)
    step = 2 * radius / cells
    step_fraction = Fraction(65536001, 10000000 * 1280)
    families = load_families()
    signs = {}
    for sigma in (mp.mpf("-0.5"), mp.mpf("0.5")):
        nodes = []
        total = Fraction(0)
        for index in range(cells + 1):
            x_exact = Fraction(-65536001, 10000000) + index * step_fraction
            x = mp.mpf(x_exact.numerator) / mp.mpf(x_exact.denominator)
            center_norm, error, weight, upper = node_parts(families, x, sigma)
            upper_fraction = upward_binary_fraction(upper)
            nodes.append(
                {
                    "index": index,
                    "x": str(x),
                    "x_exact": f"{x_exact.numerator}/{x_exact.denominator}",
                    "center_norm": mp.nstr(center_norm, 60),
                    "coefficient_error": mp.nstr(error, 60),
                    "weight": mp.nstr(weight, 60),
                    "weighted_upper": mp.nstr(upper, 60),
                    "weighted_upper_binary_rational": f"{upper_fraction.numerator}/{upper_fraction.denominator}",
                }
            )
            if index < cells:
                next_x_exact = Fraction(-65536001, 10000000) + (index + 1) * step_fraction
                next_x = mp.mpf(next_x_exact.numerator) / mp.mpf(next_x_exact.denominator)
                next_upper = node_parts(families, next_x, sigma)[3]
                next_fraction = upward_binary_fraction(next_upper)
                total += step_fraction / 2 * (upper_fraction + next_fraction)
        signs[str(sigma)] = {
            "nodes": nodes,
            "node_sum_binary_rational": f"{total.numerator}/{total.denominator}",
            "node_sum_binary_float": float(total),
        }

    payload = {
        "record": 2530,
        "status": "CENTER_PLUS_SCALAR_ERROR_NODE_PAYLOAD_DIAGNOSTIC",
        "cells": cells,
        "node_count": cells + 1,
        "radius": str(radius),
        "step": str(step),
        "coefficient_representation": "2338 box midpoint plus Euclidean radius charge",
        "node_arithmetic": "mpmath 100 decimal digits; upward binary64 rational export",
        "signs": signs,
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": ["no Lean transcendental enclosure", "no curvature payload", "no producer GO", "no SourceRH", "no RH"],
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"record": 2530, "status": payload["status"], "cells": cells, "node_sum_binary_float": {k: v["node_sum_binary_float"] for k, v in signs.items()}, "artifact": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
