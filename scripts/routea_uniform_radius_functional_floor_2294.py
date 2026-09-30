"""2294: price the independent uniform-radius functional propagation floor.

This is a lower bound on a CHOSEN positive error majorant, never a lower bound
on the actual transform error or the signed Weil functional.
"""
import argparse
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp

import routea_interval_fifth_derivative_preflight_2292 as owner

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results/2293_grouped_centered_derivative_preflight.json"
OUT = ROOT / "results/2294_uniform_radius_functional_floor.json"


def enumerate_prime_powers(limit):
    sieve = bytearray([1])*(limit + 1)
    sieve[:2] = bytes(min(2, limit + 1))
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            start = prime*prime
            sieve[start:limit + 1:prime] = bytes((limit - start)//prime + 1)
    powers = []
    for prime in range(2, limit + 1):
        if sieve[prime]:
            number = prime
            while number <= limit:
                powers.append((number, prime))
                number *= prime
    return sorted(powers)


def squared_product_error_majorant(base_size, corr_size, base_radius, corr_radius):
    if any(value < 0 for value in (base_size, corr_size, base_radius, corr_radius)):
        raise ValueError("sizes and radii must be nonnegative")
    base_error = 2*base_size*base_radius + base_radius**2
    corr_error = 2*corr_size*corr_radius + corr_radius**2
    return base_size**2*corr_error + corr_size**2*base_error + base_error*corr_error


def interval_text(box):
    endpoints = {}
    for name, raw, rounding in (("lower", box._mpi_[0], ROUND_FLOOR),
                                ("upper", box._mpi_[1], ROUND_CEILING)):
        sign, mantissa, exponent, _ = raw
        exact = Fraction((-1 if sign else 1)*mantissa)*Fraction(2)**exponent
        with localcontext() as context:
            context.prec = 45
            context.rounding = rounding
            endpoints[name] = str(Decimal(exact.numerator)/Decimal(exact.denominator))
    return endpoints


def price_weight_cell(families, eta, gamma):
    half = max(mp.mpf(width)**2 for width, _ in families)
    limit_box = mp.iv.exp(2*mp.iv.mpf(half))
    lower_limit = int(mp.floor(owner.lower(limit_box)))
    upper_limit = int(mp.floor(owner.upper(limit_box)))
    if lower_limit != upper_limit:
        raise ArithmeticError("prime-power cutoff integer is unresolved")
    powers = enumerate_prime_powers(lower_limit)
    if len(powers) != 41136:
        raise ValueError("corrected-owner prime-power count guard failed")
    eta_box = mp.iv.mpf(eta)
    angular_radius = 2*mp.iv.pi*eta_box
    if owner.upper((mp.iv.pi*eta_box)**2) > mp.mpf(3)/16:
        raise ValueError("digamma nonnegative-sigma guard fails")
    kernel_lower_box = mp.iv.mpf(0)
    for number, prime in powers:
        angle_size = angular_radius*mp.iv.log(number)
        cosine_lower = 1-angle_size**2/2
        if owner.lower(cosine_lower) <= 0:
            raise ValueError("cell too wide for positive visible-prime guard")
        kernel_lower_box += 2*mp.iv.log(prime)/mp.iv.sqrt(number)*cosine_lower
    height_distance = mp.iv.mpf(gamma) - angular_radius
    if owner.lower(height_distance) <= 0:
        raise ValueError("annihilator factor distance reaches zero")
    polynomial_squared_lower_box = height_distance**8
    weight_integral_lower_box = 2*eta_box*kernel_lower_box*polynomial_squared_lower_box
    return {"support_half_width": mp.nstr(half, 45), "cutoff": lower_limit,
            "prime_power_count": len(powers), "cell": ["-" + eta, eta],
            "kernel_lower_price": interval_text(kernel_lower_box),
            "polynomial_squared_lower_price": interval_text(polynomial_squared_lower_box),
            "weight_integral_lower_price": interval_text(weight_integral_lower_box)}, weight_integral_lower_box


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--eta", default="0.00001")
    parser.add_argument("--budget", default="10000000")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    mp.mp.dps = mp.iv.dps = 80
    if mp.mpf(args.eta) <= 0 or mp.mpf(args.budget) <= 0:
        parser.error("eta and budget must be positive")
    artifact = json.loads(INPUT.read_text(encoding="utf-8"))
    capture, families, _, _ = owner.owner_source.load_owner()
    capture_hash = hashlib.sha256(owner.owner_source.CAPTURE.read_bytes()).hexdigest()
    if artifact["owner_capture_sha256"] != capture_hash:
        raise ValueError("2293 owner capture hash mismatch")
    target_nodes = capture["owner_capture"]["nodes_hex"][:4]
    gamma = abs(float.fromhex(target_nodes[0][1]))
    if not all(abs(float.fromhex(node[1])) == gamma for node in target_nodes):
        raise ValueError("four-point annihilator height guard failed")
    weight, weight_box = price_weight_cell(families, args.eta, gamma)
    weight_floor = mp.iv.mpf(owner.lower(weight_box))
    rows = []
    budget = mp.iv.mpf(args.budget)
    for reading in artifact["partition_readings"]:
        base_radius = mp.iv.mpf(reading["base"]["lobatto_integrated_panel_proxy"]["centered_fifth_bound"])
        corr_radius = mp.iv.mpf(reading["corr"]["lobatto_integrated_panel_proxy"]["centered_fifth_bound"])
        quartic_floor = base_radius**2*corr_radius**2
        charge_floor = weight_floor*quartic_floor
        ratio = charge_floor/budget
        uniform_scale_ceiling = mp.iv.exp(mp.iv.log(budget/charge_floor)/4)
        rows.append({"subcells_per_panel": reading["subcells_per_panel"],
                     "base_radius": interval_text(base_radius), "corr_radius": interval_text(corr_radius),
                     "quartic_majorant_floor": interval_text(quartic_floor),
                     "cell_majorant_charge_floor": interval_text(charge_floor),
                     "budget_ratio_floor": interval_text(ratio),
                     "common_radius_scale_necessary_ceiling": interval_text(uniform_scale_ceiling),
                     "method_over_budget": owner.lower(ratio) > 1})
    result = {"record": 2294, "status": "SCOPED-NO-GO-UNIFORM-INDEPENDENT-RADIUS-PROPAGATION"
              if all(row["method_over_budget"] for row in rows) else "PROPAGATION-FLOOR-INCONCLUSIVE",
              "certificate": False, "hgap_closed": False, "budget": args.budget,
              "endpoint_encoding": "45-digit decimal ROUND_FLOOR/ROUND_CEILING from exact binary interval endpoints",
              "owner_capture_sha256": capture_hash, "gamma_stored": gamma,
              "weight_cell": weight, "rows": rows,
              "source_sha256": {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (INPUT, Path(__file__))},
              "scope": "advertised 2293 decimal radii, independent uniform balls, absolute propagation on one origin cell",
              "nonclaims": ["floor on a chosen majorant, not on actual error or signed functional",
                            "origin-cell ruling applies to windows containing this cell, not to tail-only intervals",
                            "no verdict on correlated, frequency-dependent or direct-functional mechanisms",
                            "rounding allowances and full-window/infinite-tail charges are omitted",
                            "stored owner is not an actual selected-owner readback",
                            "no hgap supplier, producer GO or RH claim"]}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(result["status"])
    print(json.dumps({"prime_power_count": weight["prime_power_count"], "rows": [
        {"subcells": row["subcells_per_panel"], "ratio_floor": row["budget_ratio_floor"]["lower"],
         "scale_ceiling": row["common_radius_scale_necessary_ceiling"]["upper"]} for row in rows]}))


if __name__ == "__main__":
    main()
