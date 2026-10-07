"""Price an exact polynomial ODE-residual architecture for actual entry (0,0).

No numerical integration backend is used. Scalar exponentials use Arb balls;
their Lean certification and the panel assembly remain separate obligations.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

import flint
from flint import arb, ctx, fmpq

ROOT = Path(__file__).resolve().parents[1]


def rational(value):
    value = Fraction(value)
    return fmpq(value.numerator, value.denominator)


def ball(value):
    return arb(value.numerator) / arb(value.denominator)


def multiply(left, right):
    result = [fmpq(0) for _ in range(len(left) + len(right) - 1)]
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] += left_value * right_value
    return result


def subtract(left, right):
    result = [fmpq(0) for _ in range(max(len(left), len(right)))]
    for index, value in enumerate(left):
        result[index] += value
    for index, value in enumerate(right):
        result[index] -= value
    return result


def build_panel(beta, center, half_width, degree):
    if degree < 1 or half_width <= 0 or abs(center) + half_width >= 1:
        raise ValueError("positive degree and nonsingular interior panel required")
    deficit = [1 - center * center, -2 * center, fmpq(-1)]
    denominator = multiply(deficit, deficit)
    numerator = [beta * value for value in denominator]
    numerator[0] -= 60 * center
    numerator[1] -= 60
    coefficients = [fmpq(1)]
    for order in range(degree):
        rhs = sum((numerator[index] * coefficients[order - index]
                   for index in range(min(4, order) + 1)), fmpq(0))
        lhs = sum((denominator[index] * (order - index + 1) *
                   coefficients[order - index + 1]
                   for index in range(1, min(4, order) + 1)), fmpq(0))
        coefficients.append((rhs - lhs) / (denominator[0] * (order + 1)))
    derivative = [index * coefficients[index] for index in range(1, len(coefficients))]
    residual = subtract(multiply(denominator, derivative), multiply(numerator, coefficients))
    if any(residual[:degree]):
        raise RuntimeError("exact low-order residual identity failed")
    residual_upper = sum((abs(value) * half_width ** index
                          for index, value in enumerate(residual)), fmpq(0))
    edge = abs(center) + half_width
    denominator_lower = (1 - edge * edge) ** 2
    residual_quotient = residual_upper / denominator_lower
    phase_variation = (abs(beta) + 60 * edge / denominator_lower) * half_width
    integral_polynomial = sum((2 * coefficients[index] * half_width ** (index + 1) /
                               (index + 1) for index in range(0, degree + 1, 2)), fmpq(0))
    return {"coefficients": coefficients, "residual": residual,
            "residual_quotient": residual_quotient, "phase_variation": phase_variation,
            "integral_polynomial": integral_polynomial}


def serialize(value):
    if not value.is_finite():
        raise ValueError("nonfinite scalar enclosure")
    return {"lower_exact": str(value.lower().fmpq()),
            "upper_exact": str(value.upper().fmpq()), "display": value.str(15)}


def run(degrees=(32, 48, 64), panels=180, cut=Fraction(9, 10), precision=384):
    if panels <= 0 or not 0 < cut < 1 or precision < 256 or not degrees:
        raise ValueError("positive panel count, interior cut, and >=256 bits required")
    ctx.prec = precision
    started = time.monotonic()
    capture_path = ROOT / "results/2275_gap_owner_audit.json"
    witness_path = ROOT / "results/2351_moment_matrix_witness.json"
    capture = json.loads(capture_path.read_text())["owner_capture"]
    witness_payload = json.loads(witness_path.read_text())
    witness = witness_payload["matrix"][0][0]["real"]
    width, modulation = map(lambda value: rational(float.fromhex(value)), capture["families_hex"][0])
    node_real, node_imag = map(lambda value: rational(float.fromhex(value)), capture["nodes_hex"][0])
    if node_imag + modulation != 0:
        raise ValueError("entry (0,0) phase must cancel exactly")
    radius = width * width
    if radius != rational(witness_payload["support_radii_exact"][0]):
        raise ValueError("physical support radius differs from the committed witness")
    beta = node_real * radius
    cut = rational(cut)
    half_width = cut / panels
    edge_charge = ball(2 * radius * (1 - cut)) * ball(-30 / (1 - cut * cut) + abs(beta)).exp()
    target_lo, target_hi = rational(witness["lower_exact"]), rational(witness["upper_exact"])
    rows = []
    for degree in degrees:
        integral, charge = arb(0), arb(0)
        digest = hashlib.sha256()
        for index in range(panels):
            center = -cut + (2 * index + 1) * half_width
            panel = build_panel(beta, center, half_width, degree)
            amplitude = ball(-30 / (1 - center * center) + beta * center).exp()
            integral += amplitude * ball(panel["integral_polynomial"])
            charge += amplitude * ball(2 * half_width ** 2 * panel["residual_quotient"]) * (
                2 * ball(panel["phase_variation"])).exp()
            for value in panel["coefficients"] + panel["residual"]:
                digest.update((str(value) + "\n").encode())
        core = ball(radius) * integral
        interior_charge = (ball(radius) * charge).upper()
        lower = core.lower() - interior_charge
        upper = core.upper() + interior_charge + edge_charge.upper()
        contained = lower > ball(target_lo) and upper < ball(target_hi)
        rows.append({"degree": degree, "panels": panels,
                     "coefficient_and_residual_sha256": digest.hexdigest(),
                     "low_order_residual_identities_exact": True,
                     "core_integral": serialize(core), "interior_charge": serialize(interior_charge),
                     "lower_bound": serialize(lower), "upper_bound": serialize(upper),
                     "lower_margin": serialize(lower - ball(target_lo)),
                     "upper_margin": serialize(ball(target_hi) - upper),
                     "fits_2597_under_stability_and_edge_bounds": bool(contained)})
        print(f"degree={degree} panels={panels} fits={contained} charge={interior_charge.str(8)}", flush=True)
    return {"record": 2619, "status": "EXACT_RESIDUAL_MODEL_PRICED_NOT_LEAN_CONTAINMENT",
            "entry": [0, 0], "radius_exact": str(radius), "beta_exact": str(beta),
            "cut_exact": str(cut), "precision_bits": precision,
            "python_flint_version": flint.__version__, "support_radius_matches_witness": True,
            "edge_charge": serialize(edge_charge), "rows": rows,
            "capture_sha256": hashlib.sha256(capture_path.read_bytes()).hexdigest(),
            "witness_sha256": hashlib.sha256(witness_path.read_bytes()).hexdigest(),
            "probe_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "integration_backend_used": False,
            "formal_obligations": {
                "same_owner_phase_derivative": "generic_theorem_verified_in_2619",
                "integrating_factor_stability": "generic_theorem_verified_in_2619",
                "rational_polynomial_recurrence_and_integral": "numeric_tables_not_verified_in_Lean",
                "scalar_exponential_balls": "external_Arb_only",
                "edge_integral_bound": "generic_theorem_verified_numeric_exponential_not_attached",
                "partition_assembly": "not_verified_in_Lean"},
            "actual_entry_containment_lean_verified": False,
            "producer_go": False, "rh_claim": False,
            "elapsed_seconds": time.monotonic() - started}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, nargs="+", default=[32, 48, 64])
    parser.add_argument("--panels", type=int, default=180)
    parser.add_argument("--precision", type=int, default=384)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/2619_analytic_moment_residual_probe.json")
    arguments = parser.parse_args()
    result = run(tuple(arguments.degree), arguments.panels, precision=arguments.precision)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
