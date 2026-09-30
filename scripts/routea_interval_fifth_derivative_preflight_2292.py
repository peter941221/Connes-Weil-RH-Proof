"""2292: grouped fifth-derivative interval instrument repair.

Interior enclosures are diagnostic only. Edge-crossing cells remain explicitly
unresolved; no full-support, integral, hgap, or producer certificate is claimed.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_phase_centered_filon_tail_screen_2280 as owner_source

OUT = ROOT / "results/2292_interval_fifth_derivative_preflight.json"


class SupportEdgeError(ValueError):
    pass


def lower(value):
    return mp.mpf(value._mpi_[0])


def upper(value):
    return mp.mpf(value._mpi_[1])


def fifth_log_polynomial(first, second, third, fourth, fifth):
    return (first**5 + 10*first**3*second + 15*first*second**2
            + 10*first**2*third + 10*second*third + 5*first*fourth + fifth)


def owner_fifth_iv(coordinates, families, coefficients):
    if len(families) != len(coefficients):
        raise ValueError("family/coefficient length mismatch")
    total = mp.iv.mpc(0)
    for coefficient, (width, theta) in zip(coefficients, families):
        radius = mp.iv.mpf(width)**2
        if lower(coordinates) >= upper(radius) or upper(coordinates) <= -upper(radius):
            continue
        if lower(coordinates) <= -lower(radius) or upper(coordinates) >= lower(radius):
            raise SupportEdgeError("cell intersects a family support endpoint")
        radius_squared = radius**2
        quotient = 1 - coordinates**2 / radius_squared
        if lower(quotient) <= 0:
            raise SupportEdgeError("interval quotient reaches zero")
        multiplier = mp.iv.mpc(float(coefficient.real), float(coefficient.imag))
        exponent = mp.iv.mpc(0.5, theta)
        first = exponent - 60*coordinates/(radius_squared*quotient**2)
        second = -60*(radius_squared + 3*coordinates**2)/(radius**4*quotient**3)
        third = -720*coordinates*(radius_squared + coordinates**2)/(radius**6*quotient**4)
        fourth = -720*(radius**4 + 10*radius_squared*coordinates**2
                       + 5*coordinates**4)/(radius**8*quotient**5)
        fifth = -7200*coordinates*(radius_squared + 3*coordinates**2)*(
            3*radius_squared + coordinates**2)/(radius**10*quotient**6)
        profile = mp.iv.exp(-30/quotient + exponent*coordinates)
        total += multiplier*profile*fifth_log_polynomial(first, second, third, fourth, fifth)
    return total


def modulus_upper(value):
    return upper(mp.iv.sqrt(value.real**2 + value.imag**2))


def bound(families, coefficients, panels, subcells):
    half = max(mp.mpf(width)**2 for width, _ in families)
    length = 2*half/panels
    rows = []
    unresolved = []
    maximum = mp.mpf(0)
    for panel in range(panels):
        for subcell in range(subcells):
            left = -half + length*(panel + mp.mpf(subcell)/subcells)
            right = -half + length*(panel + mp.mpf(subcell + 1)/subcells)
            coordinates = mp.iv.mpf([left, right])
            try:
                derivative = owner_fifth_iv(coordinates, families, coefficients)
            except SupportEdgeError as error:
                unresolved.append({"panel": panel, "subcell": subcell, "reason": str(error)})
                continue
            reading = modulus_upper(derivative)
            if not mp.isfinite(reading):
                raise ArithmeticError("nonfinite interior derivative enclosure")
            maximum = max(maximum, reading)
            rows.append({"panel": panel, "subcell": subcell, "bound": mp.nstr(reading, 30)})
    proxy = panels*(length/2)**5/mp.factorial(5)*maximum
    return {
        "subcells_per_panel": subcells,
        "covered_cells": len(rows),
        "unresolved_edge_cells": len(unresolved),
        "max_interval_bound": mp.nstr(maximum, 30),
        "legacy_amplitude_proxy": mp.nstr(proxy, 30),
        "interior_integrated_remainder_proxy": mp.nstr(length*proxy, 30),
        "full_support_bound": False,
        "unresolved": unresolved,
        "rows": rows,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--subcells", type=int, default=8)
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    if args.subcells <= 0:
        parser.error("--subcells must be positive")
    _, families, base, correction = owner_source.load_owner()
    mp.mp.dps = mp.iv.dps = 70
    result = {
        "record": 2292,
        "status": "REPAIRED-INTERIOR-INTERVAL-PREFLIGHT",
        "certificate": False,
        "hgap_closed": False,
        "panels": 24,
        "degree": 4,
        "derivative_order": 5,
        "owner": {"family_count": len(families), "input_convention": "exact stored binary64 operands",
                  "capture_sha256": hashlib.sha256(owner_source.CAPTURE.read_bytes()).hexdigest()},
        "withdrawn": ["old enormous prices evaluated outside support and used wrong derivative numerators",
                      "old max component reading was not a complex modulus upper bound",
                      "old partition no-go is withdrawn; no corrected method no-go is registered"],
        "base": bound(families, base, 24, args.subcells),
        "corr": bound(families, correction, 24, args.subcells),
        "nonclaims": ["support-edge cells unresolved; interior proxy is not a full-support bound",
                      "legacy amplitude proxy omits panel length; integrated proxy restores it",
                      "pointwise derivative enclosures do not certify the functional integral",
                      "mpmath.iv is not the project directed-MPFR certificate",
                      "finite window, infinite tail, owner readback, and functional propagation remain open",
                      "no hgap supplier, producer GO or RH claim"],
    }
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({channel: {key: result[channel][key] for key in (
        "max_interval_bound", "legacy_amplitude_proxy", "unresolved_edge_cells")}
        for channel in ("base", "corr")}))


if __name__ == "__main__":
    main()
