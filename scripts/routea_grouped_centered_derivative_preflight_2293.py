"""2293: grouped centered fifth derivative with a sixth-derivative variation bound.

Truncated Taylor algebra encloses derivatives; endpoint-crossing families use
flat-extension envelopes. This is not a functional-integral/hgap certificate.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp

import routea_interval_fifth_derivative_preflight_2292 as repaired

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/2293_grouped_centered_derivative_preflight.json"


def multiply_polynomials(left, right):
    result = [mp.iv.mpf(0) for _ in range(len(left) + len(right) - 1)]
    for first, value in enumerate(left):
        for second, other in enumerate(right):
            result[first + second] += value*other
    return result


def log_numerators(radius, order):
    inverse_radius_squared = 1/radius**2
    numerator = [mp.iv.mpf(0), -60*inverse_radius_squared]
    output = [numerator]
    for index in range(1, order):
        derivative = [(degree + 1)*numerator[degree + 1]
                      for degree in range(len(numerator) - 1)]
        first = multiply_polynomials(derivative, [mp.iv.mpf(1), mp.iv.mpf(0), -inverse_radius_squared])
        second = multiply_polynomials(numerator, [mp.iv.mpf(0), 2*(index + 1)*inverse_radius_squared])
        numerator = [mp.iv.mpf(0) for _ in range(max(len(first), len(second)))]
        for slot, value in enumerate(first):
            numerator[slot] += value
        for slot, value in enumerate(second):
            numerator[slot] += value
        output.append(numerator)
    return output


def flat_edge_bound(coordinates, width, theta, coefficient, order):
    radius = mp.iv.mpf(width)**2
    clipped_left = max(repaired.lower(coordinates), -repaired.upper(radius))
    clipped_right = min(repaired.upper(coordinates), repaired.upper(radius))
    if clipped_left >= clipped_right:
        return mp.iv.mpf(0)
    clipped = mp.iv.mpf([clipped_left, clipped_right])
    quotient = 1 - clipped**2/radius**2
    quotient_upper = min(mp.mpf(1), repaired.upper(quotient))
    if quotient_upper <= 0:
        return mp.iv.mpf(0)
    quotient_box = mp.iv.mpf(quotient_upper)
    coordinate_size = mp.iv.mpf(max(abs(clipped_left), abs(clipped_right)))
    numerators = log_numerators(radius, order)
    logarithms = []
    for index, polynomial in enumerate(numerators, start=1):
        magnitude = sum((abs(value)*coordinate_size**degree
                         for degree, value in enumerate(polynomial)), mp.iv.mpf(0))
        logarithms.append(magnitude/quotient_box**(index + 1))
    logarithms[0] += abs(mp.iv.mpc(0.5, theta))
    bell = [mp.iv.mpf(1)]
    for degree in range(1, order + 1):
        bell.append(sum((math.comb(degree - 1, index - 1)*logarithms[index - 1]*bell[degree - index]
                         for index in range(1, degree + 1)), mp.iv.mpf(0)))
    if 2*order*quotient_upper > 30:
        raise ValueError("flat-envelope monotonicity range exceeded")
    return abs(mp.iv.mpc(float(coefficient.real), float(coefficient.imag)))*mp.iv.exp(
        -30/quotient_box + mp.iv.mpf(clipped_right)/2)*bell[order]


def family_jet(coordinates, width, theta, coefficient, order):
    radius = mp.iv.mpf(width)**2
    quotient = [1 - coordinates**2/radius**2, -2*coordinates/radius**2, -1/radius**2]
    if repaired.lower(quotient[0]) <= 0:
        raise repaired.SupportEdgeError("nonpositive quotient in interior jet")
    reciprocal = [1/quotient[0]]
    for degree in range(1, order + 1):
        reciprocal.append(-sum((quotient[index]*reciprocal[degree - index]
                               for index in range(1, min(degree, 2) + 1)), mp.iv.mpf(0))/quotient[0])
    exponent = mp.iv.mpc(0.5, theta)
    logarithm = [-30*value for value in reciprocal]
    logarithm[0] += exponent*coordinates
    logarithm[1] += exponent
    jet = [mp.iv.exp(logarithm[0])]
    for degree in range(1, order + 1):
        jet.append(sum((index*logarithm[index]*jet[degree - index]
                       for index in range(1, degree + 1)), mp.iv.mpc(0))/degree)
    return mp.iv.mpc(float(coefficient.real), float(coefficient.imag))*jet[order]*math.factorial(order)


def grouped_derivative(coordinates, families, coefficients, order):
    total = mp.iv.mpc(0)
    edges = 0
    for coefficient, (width, theta) in zip(coefficients, families):
        radius = mp.iv.mpf(width)**2
        if repaired.lower(coordinates) >= repaired.upper(radius) or repaired.upper(coordinates) <= -repaired.upper(radius):
            continue
        if repaired.lower(coordinates) <= -repaired.lower(radius) or repaired.upper(coordinates) >= repaired.lower(radius):
            envelope = flat_edge_bound(coordinates, width, theta, coefficient, order)
            bound = repaired.upper(envelope)
            symmetric = mp.iv.mpf([-bound, bound])
            total += mp.iv.mpc(symmetric, symmetric)
            edges += 1
        else:
            total += family_jet(coordinates, width, theta, coefficient, order)
    return total, edges


def price(families, coefficients, subcells, panels=24):
    half = max(mp.mpf(width)**2 for width, _ in families)
    length = 2*half/panels
    rows = []
    for panel in range(panels):
        panel_direct = mp.mpf(0)
        panel_centered = mp.mpf(0)
        edge_terms = 0
        for subcell in range(subcells):
            left = -half + length*(panel + mp.mpf(subcell)/subcells)
            right = -half + length*(panel + mp.mpf(subcell + 1)/subcells)
            box = mp.iv.mpf([left, right])
            center = (box.a + box.b)/2
            cell_radius = (box.b - box.a)/2
            direct, edge_count = grouped_derivative(box, families, coefficients, 5)
            centered, _ = grouped_derivative(center, families, coefficients, 5)
            sixth, _ = grouped_derivative(box, families, coefficients, 6)
            centered_bound = abs(centered) + cell_radius*abs(sixth)
            direct_bound = repaired.modulus_upper(direct)
            variation_bound = repaired.upper(centered_bound)
            if not mp.isfinite(direct_bound) or not mp.isfinite(variation_bound):
                raise ArithmeticError("nonfinite derivative enclosure")
            edge_terms += edge_count
            panel_direct = max(panel_direct, direct_bound)
            panel_centered = max(panel_centered, min(direct_bound, variation_bound))
        rows.append({"panel": panel, "direct_fifth_bound": mp.nstr(panel_direct, 30),
                     "centered_fifth_bound": mp.nstr(panel_centered, 30),
                     "edge_family_cells": edge_terms})
    maxima = {key: max(mp.mpf(row[key]) for row in rows)
              for key in ("direct_fifth_bound", "centered_fifth_bound")}
    shape = (length/2)**5/mp.factorial(5)
    return {"subcells_per_panel": subcells, "cells": panels*subcells,
            "full_support_covered": True,
            "edge_family_cells": sum(row["edge_family_cells"] for row in rows),
            "global_bounds": {key: mp.nstr(value, 30) for key, value in maxima.items()},
            "legacy_global_proxy": {key: mp.nstr(panels*shape*value, 30) for key, value in maxima.items()},
            "integrated_panel_proxy": {key: mp.nstr(length*shape*sum(mp.mpf(row[key]) for row in rows), 30)
                                       for key in maxima},
            "lobatto_integrated_panel_proxy": {key: mp.nstr(
                (length/2)**6/(8*mp.factorial(5))*sum(mp.mpf(row[key]) for row in rows), 30)
                for key in maxima}, "rows": rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--subcells", type=int, default=8)
    parser.add_argument("--ladder", default="")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    if args.subcells <= 0:
        parser.error("--subcells must be positive")
    ladder = [int(value) for value in args.ladder.split(",")] if args.ladder else [args.subcells]
    if any(value <= 0 for value in ladder):
        parser.error("ladder entries must be positive")
    mp.mp.dps = mp.iv.dps = 70
    _, families, base, correction = repaired.owner_source.load_owner()
    readings = [{"subcells_per_panel": subdivision,
                 "base": price(families, base, subdivision),
                 "corr": price(families, correction, subdivision)} for subdivision in ladder]
    result = {"record": 2293, "status": "GROUPED-CENTERED-DERIVATIVE-PREFLIGHT",
              "certificate": False, "hgap_closed": False,
              "owner_capture_sha256": hashlib.sha256(repaired.owner_source.CAPTURE.read_bytes()).hexdigest(),
              "input_convention": "exact stored binary64 operands", "panels": 24, "degree": 4,
              "base": readings[-1]["base"], "corr": readings[-1]["corr"],
              "partition_readings": readings,
              "nonclaims": ["derivative preflight, not a directed-MPFR integral certificate",
                            "proxy is a Laplace interpolation error size, not the kernel-weighted functional charge",
                            "infinite xi tail, interpolation arithmetic and owner readback remain open",
                            "no hgap supplier, producer GO or RH claim"]}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({channel: {key: result[channel][key] for key in (
        "global_bounds", "legacy_global_proxy", "lobatto_integrated_panel_proxy", "edge_family_cells")}
        for channel in ("base", "corr")}))


if __name__ == "__main__":
    main()
