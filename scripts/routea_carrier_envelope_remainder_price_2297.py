"""2297: price seventh-derivative carrier-envelope interpolation bounds.

Grouped within carriers, triangle summed across carriers. This is a diagnostic
of a named bound method, not a signed-functional integral certificate.
"""
import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp

import routea_carrier_separated_functional_screen_2296 as carrier
import routea_grouped_centered_derivative_preflight_2293 as jets
import routea_uniform_radius_functional_floor_2294 as propagation

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/2297_carrier_envelope_remainder_price.json"


def channel_coefficients(families, coefficients):
    groups = []
    for theta, indices in carrier.carrier_groups(families):
        by_width = defaultdict(lambda: mp.iv.mpc(0))
        for index in indices:
            coefficient = coefficients[index]
            by_width[families[index][0]] += mp.iv.mpc(float(coefficient.real), float(coefficient.imag))
        groups.append((theta, dict(by_width)))
    return groups


def price(families, base, correction, panels, subcells):
    half = max(mp.mpf(width)**2 for width, _ in families)
    length = 2*half/panels
    widths = sorted(set(width for width, _ in families))
    channels = {"base": channel_coefficients(families, base),
                "corr": channel_coefficients(families, correction)}
    rows = []
    totals = {name: mp.iv.mpf(0) for name in channels}
    for panel in range(panels):
        bounds = {name: [mp.mpf(0) for _ in groups] for name, groups in channels.items()}
        edge_calls = 0
        for subcell in range(subcells):
            left = -half + length*(panel + mp.mpf(subcell)/subcells)
            right = -half + length*(panel + mp.mpf(subcell + 1)/subcells)
            box = mp.iv.mpf([left, right])
            center = (box.a + box.b)/2
            cell_radius = (box.b-box.a)/2
            cache = {}
            for width in widths:
                seventh, edges = jets.grouped_derivative(box, [(width, 0.0)], [1+0j], 7)
                centered, _ = jets.grouped_derivative(center, [(width, 0.0)], [1+0j], 7)
                eighth, _ = jets.grouped_derivative(box, [(width, 0.0)], [1+0j], 8)
                cache[width] = (seventh, centered, eighth)
                edge_calls += edges
            for name, groups in channels.items():
                for index, (_, coefficients) in enumerate(groups):
                    direct = sum((coefficient*cache[width][0] for width, coefficient in coefficients.items()), mp.iv.mpc(0))
                    center_value = sum((coefficient*cache[width][1] for width, coefficient in coefficients.items()), mp.iv.mpc(0))
                    eighth = sum((coefficient*cache[width][2] for width, coefficient in coefficients.items()), mp.iv.mpc(0))
                    bound = min(jets.repaired.modulus_upper(direct),
                                jets.repaired.upper(abs(center_value) + cell_radius*abs(eighth)))
                    bounds[name][index] = max(bounds[name][index], bound)
        row = {"panel": panel, "edge_shape_cells": edge_calls}
        for name, maxima in bounds.items():
            charge = (mp.iv.mpf(length)/2)**8/(32*math.factorial(7))*sum(
                (mp.iv.mpf(maximum) for maximum in maxima), mp.iv.mpf(0))
            row[name+"_panel_radius"] = propagation.interval_text(charge)
            totals[name] += charge
        rows.append(row)
    return {"panels": panels, "degree": 6, "subcells": subcells,
            "unique_shapes": len(widths), "carrier_count": len(channels["base"]),
            "base_radius": propagation.interval_text(totals["base"]),
            "corr_radius": propagation.interval_text(totals["corr"]),
            "rows": rows}, totals


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--panels", type=int, default=192)
    parser.add_argument("--subcells", type=int, default=2)
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    if args.panels <= 0 or args.subcells <= 0:
        parser.error("panels and subcells must be positive")
    mp.mp.dps = mp.iv.dps = 70
    _, families, base, correction = carrier.SOURCE.load_owner()
    reading, totals = price(families, base, correction, args.panels, args.subcells)
    weight, weight_box = propagation.price_weight_cell(families, "0.00001", carrier.SOURCE.GAMMA)
    floor = mp.iv.mpf(jets.repaired.lower(weight_box))*totals["base"]**2*totals["corr"]**2
    ratio = floor/10000000
    result = {"record": 2297, "status": "CARRIER-ENVELOPE-REMAINDER-METHOD-PRICE",
              "certificate": False, "hgap_closed": False, "reading": reading,
              "origin_majorant_floor": propagation.interval_text(floor),
              "origin_floor_budget_ratio": propagation.interval_text(ratio),
              "origin_floor_over_budget": jets.repaired.lower(ratio) > 1,
              "weight_cell": weight,
              "source_sha256": {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (carrier.SOURCE.CAPTURE, Path(jets.__file__), Path(propagation.__file__), Path(__file__))},
              "nonclaims": ["carrierwise triangle bound discards inter-carrier correlation",
                            "a lower-priced origin floor is necessary but not sufficient for functional propagation",
                            "finite-window quadrature and moment/node arithmetic remain open",
                            "partition assembly is diagnostic, not an exact selected-owner certificate",
                            "no infinite-tail bound, hgap supplier, producer GO or RH claim"]}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({key: reading[key] for key in ("base_radius", "corr_radius", "panels", "subcells")}))
    print(json.dumps({"origin_floor_budget_ratio": result["origin_floor_budget_ratio"],
                      "over_budget": result["origin_floor_over_budget"]}))


if __name__ == "__main__":
    main()
