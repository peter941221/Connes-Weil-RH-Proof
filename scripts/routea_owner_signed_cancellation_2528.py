"""2528: signed pointwise cancellation feasibility probe.

This is a routing diagnostic, not a Lean certificate.  It changes two named
parameters of the blocked 2471 wide-box route:

1. evaluate the 30-family sum at each grid node before taking the modulus;
2. evaluate the weighted second derivative of the 30-family sum before taking
   the modulus, then price the composite-trapezoid remainder cellwise.

The coefficient is represented by the midpoint of each 2338 exact box plus a
separate Euclidean box-radius charge.  Nodes use high-precision mpmath.  The
cell curvature maximum is a resolved subgrid diagnostic; it is deliberately
not called a proof because a sampled maximum is not an enclosure.
"""
from __future__ import annotations

import hashlib
import json
import math
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2528_signed_pointwise_cancellation_probe.json"
mp.mp.dps = 100


def q(text: str) -> mp.mpf:
    a, b = text.split("/") if "/" in text else (text, "1")
    return mp.mpf(a) / mp.mpf(b)


def load_families() -> list[dict[str, mp.mpf]]:
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


def bump_terms(f: dict[str, mp.mpf], x: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf] | None:
    if abs(x) >= f["radius"]:
        return None
    u = x / f["radius"]
    qv = 1 - u * u
    bump = mp.exp(-30 / qv)
    ap = -60 * u / (f["radius"] * qv * qv)
    app = -60 * (1 + 3 * u * u) / (f["radius"] ** 2 * qv**3)
    return bump, ap, app


def point_bound(families: list[dict[str, mp.mpf]], x: mp.mpf, sigma: mp.mpf) -> mp.mpf:
    center = mp.mpc(0)
    error = mp.mpf(0)
    for f in families:
        terms = bump_terms(f, x)
        if terms is None:
            continue
        bump, _, _ = terms
        phase = mp.exp(1j * f["mod"] * x)
        center += mp.mpc(f["re"], f["im"]) * bump * phase
        error += f["err"] * bump
    return mp.exp(sigma * x) * (abs(center) + error)


def second_bound(families: list[dict[str, mp.mpf]], x: mp.mpf, sigma: mp.mpf) -> mp.mpf:
    center = mp.mpc(0)
    error = mp.mpf(0)
    for f in families:
        terms = bump_terms(f, x)
        if terms is None:
            continue
        bump, ap, app = terms
        lam = sigma + 1j * f["mod"]
        phase = mp.exp(1j * f["mod"] * x)
        factor = app + ap * ap + 2 * lam * ap + lam * lam
        center += mp.mpc(f["re"], f["im"]) * bump * phase * factor
        error += f["err"] * bump * abs(factor)
    return mp.exp(sigma * x) * (abs(center) + error)


def float_second_bound(families: list[dict[str, float]], x: float, sigma: float) -> float:
    center = 0j
    error = 0.0
    for f in families:
        if abs(x) >= f["radius"]:
            continue
        u = x / f["radius"]
        qv = 1.0 - u * u
        bump = math.exp(-30.0 / qv)
        ap = -60.0 * u / (f["radius"] * qv * qv)
        app = -60.0 * (1.0 + 3.0 * u * u) / (f["radius"] ** 2 * qv**3)
        lam = complex(sigma, f["mod"])
        factor = app + ap * ap + 2.0 * lam * ap + lam * lam
        phase = complex(math.cos(f["mod"] * x), math.sin(f["mod"] * x))
        center += complex(f["re"], f["im"]) * bump * phase * factor
        error += f["err"] * bump * abs(factor)
    return math.exp(sigma * x) * (abs(center) + error)


def run(cells: int, curvature_subnodes: int) -> dict:
    families = load_families()
    radius = mp.mpf(65536001) / mp.mpf(10000000)
    step = 2 * radius / cells
    sigma_values = [mp.mpf("-0.5"), mp.mpf("0.5")]
    result = {
        "cells": cells,
        "curvature_subnodes": curvature_subnodes,
        "radius": mp.nstr(radius, 60),
        "step": mp.nstr(step, 60),
        "signs": {},
    }
    float_families = [
        {k: float(v) for k, v in f.items()} for f in families
    ]
    for sigma in sigma_values:
        node_sum = mp.mpf(0)
        curvature_remainder = 0.0
        max_curvature = 0.0
        max_location = None
        for index in range(cells):
            x0 = -radius + index * step
            x1 = x0 + step
            y0 = point_bound(families, x0, sigma)
            y1 = point_bound(families, x1, sigma)
            node_sum += step / 2 * (y0 + y1)

            # This is a diagnostic resolved maximum, not a certified supremum.
            x0f = float(x0)
            h = float(step)
            local_max = 0.0
            local_arg = x0f
            for sub in range(curvature_subnodes + 1):
                x = x0f + h * sub / curvature_subnodes
                value = float_second_bound(float_families, x, float(sigma))
                if value > local_max:
                    local_max = value
                    local_arg = x
            curvature_remainder += h**3 * local_max / 12.0
            if local_max > max_curvature:
                max_curvature = local_max
                max_location = local_arg
        total = node_sum + mp.mpf(curvature_remainder)
        result["signs"][str(sigma)] = {
            "node_sum": mp.nstr(node_sum, 60),
            "curvature_remainder_sampled": repr(curvature_remainder),
            "total_sampled": mp.nstr(total, 60),
            "max_curvature_sampled": repr(max_curvature),
            "max_curvature_location": repr(max_location),
            "base_endpoint_margin": mp.nstr(mp.mpf("2.7790943782") - total, 60),
            "correction_endpoint_margin": mp.nstr(mp.mpf("231.2642026141") - total, 60),
        }
    result.update(
        {
            "record": 2528,
            "status": "SIGNED_POINTWISE_CANCELLATION_FEASIBILITY_DIAGNOSTIC",
            "coefficient_representation": "2338 box midpoint plus Euclidean radius charge",
            "node_arithmetic": "mpmath 100 decimal digits",
            "curvature_arithmetic": "binary64 resolved subgrid; not an enclosure",
            "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
            "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
            "nonclaims": [
                "no Lean node certificate",
                "no certified curvature supremum",
                "no producer GO",
                "no SourceRH",
                "no RH",
            ],
        }
    )
    return result


def main() -> None:
    cells = int(sys.argv[1]) if len(sys.argv) > 1 else 2560
    subnodes = int(sys.argv[2]) if len(sys.argv) > 2 else 32
    payload = run(cells, subnodes)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({
        "record": payload["record"],
        "status": payload["status"],
        "cells": cells,
        "signs": payload["signs"],
        "artifact": str(OUT),
    }, indent=2))


if __name__ == "__main__":
    main()
