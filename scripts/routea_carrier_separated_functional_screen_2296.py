"""2296: carrier-separated interpolation in the captured owner functional.

Known family phases enter the analytic moments, not the interpolated envelope.
All complex carrier contributions are summed before taking a modulus.
This is a finite-window diagnostic, not a quadrature certificate.
"""
import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path

import numpy as np

import routea_direct_functional_difference_screen_2295 as direct

SOURCE = direct.filon
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/2296_carrier_separated_functional_screen.json"


def carrier_groups(families):
    groups = defaultdict(list)
    for index, (_, theta) in enumerate(families):
        groups[theta].append(index)
    return list(groups.items())


def envelope_values(coordinates, families, coefficients, indices):
    coefficients = np.asarray(coefficients)
    if coefficients.ndim == 1:
        coefficients = coefficients[:, None]
    if coefficients.shape[0] != len(families):
        raise ValueError("coefficient/family length mismatch")
    output = np.zeros((len(coordinates), coefficients.shape[1]), dtype=complex)
    for index in indices:
        width, _ = families[index]
        radius = width*width
        quotient = 1-(coordinates/radius)**2
        profile = np.zeros_like(coordinates)
        inside = quotient > 0
        profile[inside] = np.exp(-30/quotient[inside] + 0.5*coordinates[inside])
        output += profile[:, None]*coefficients[index][None, :]
    return output


def moment_matrix(alpha, degree):
    alpha = np.asarray(alpha, dtype=float)
    output = np.empty((alpha.size, degree + 1), dtype=complex)
    small = np.abs(alpha) <= 2.0
    small_alpha = alpha[small]
    small_output = np.zeros((small_alpha.size, degree + 1), dtype=complex)
    factor = np.ones(small_alpha.size, dtype=complex)
    for order in range(100):
        for index in range(degree + 1):
            if (index + order) % 2 == 0:
                small_output[:, index] += factor*2/(index + order + 1)
        factor *= -1j*small_alpha/(order + 1)
        if factor.size == 0 or np.max(np.abs(factor)) < 1e-18:
            break
    output[small] = small_output
    large_alpha = alpha[~small]
    large_output = np.empty((large_alpha.size, degree + 1), dtype=complex)
    large_output[:, 0] = 2*np.sin(large_alpha)/large_alpha
    minus = np.exp(-1j*large_alpha)
    plus = np.exp(1j*large_alpha)
    for index in range(1, degree + 1):
        boundary = minus-((-1)**index)*plus
        large_output[:, index] = (index*large_output[:, index - 1]-boundary)/(1j*large_alpha)
    output[~small] = large_output
    return output


def separated_transform(xi, families, coefficients, panels, degree):
    coefficients = np.asarray(coefficients)
    if coefficients.ndim == 1:
        coefficients = coefficients[:, None]
    half = max(width*width for width, _ in families)
    edges = np.linspace(-half, half, panels + 1)
    nodes = np.cos(np.pi*np.arange(degree + 1)/degree)
    output = np.zeros((len(xi), coefficients.shape[1]), dtype=complex)
    for theta, indices in carrier_groups(families):
        frequency = 2*np.pi*xi-theta
        for left, right in zip(edges[:-1], edges[1:]):
            centre = (left + right)/2
            radius = (right-left)/2
            coordinates = centre+radius*nodes
            envelopes = envelope_values(coordinates, families, coefficients, indices)
            power_coefficients = np.zeros((degree + 1, coefficients.shape[1]), dtype=complex)
            for channel in range(coefficients.shape[1]):
                polynomial = np.polynomial.chebyshev.cheb2poly(
                    np.polynomial.chebyshev.chebfit(nodes, envelopes[:, channel], degree))
                power_coefficients[:len(polynomial), channel] = polynomial
            moments = moment_matrix(frequency*radius, degree)
            output += radius*np.exp(-1j*frequency*centre)[:, None]*(moments @ power_coefficients)
    return output


def identity_control(families, coefficients):
    half = max(width*width for width, _ in families)
    coordinates = np.linspace(-half, half, 257)
    direct_values = np.column_stack([SOURCE.owner_values(coordinates, families, coefficients[:, channel])
                                    for channel in range(coefficients.shape[1])])
    grouped_values = np.zeros_like(direct_values)
    absolute_book = np.zeros_like(direct_values.real)
    for theta, indices in carrier_groups(families):
        envelope = envelope_values(coordinates, families, coefficients, indices)
        grouped_values += envelope*np.exp(1j*theta*coordinates)[:, None]
        absolute_book += envelope_values(coordinates, families, np.abs(coefficients).astype(complex), indices).real
    allowance = 256*np.finfo(float).eps*np.maximum(absolute_book, np.finfo(float).tiny)
    error = np.abs(direct_values-grouped_values)
    worst = float(np.max(error/allowance))
    if worst > 1:
        raise ArithmeticError("carrier identity float-allowance control failed")
    return {"points": len(coordinates), "max_abs_deviation": float(np.max(error)),
            "allowance_ratio": worst, "passed": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", default="0.02,0.01,0.005")
    parser.add_argument("--profiles", default="24:4,24:6,48:4,48:6,96:6,192:6")
    parser.add_argument("--xi-max", type=float, default=40.0)
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    steps = [float(value) for value in args.steps.split(",")]
    profiles = [tuple(map(int, value.split(":"))) for value in args.profiles.split(",")]
    if args.xi_max <= 0 or any(value <= 0 for value in steps) or any(
            len(profile) != 2 or min(profile) <= 0 or profile[1] > 6 for profile in profiles):
        parser.error("positive window/steps/profiles required; moment preflight supports degree <= 6")
    capture, families, base, correction = SOURCE.load_owner()
    for name, vector in (("base", base), ("corr", correction)):
        if hashlib.md5(np.ascontiguousarray(vector).tobytes()).hexdigest() != capture["owner_capture"][name+"_md5"]:
            raise ValueError("stored coefficient hash guard failed")
    coefficients = np.column_stack((base, correction))
    control = identity_control(families, coefficients)
    old = json.loads((ROOT / "results/2295_direct_functional_difference_screen.json").read_text())
    rows = []
    reference_controls = []
    baseline_controls = []
    for step in steps:
        half_points = round(args.xi_max/step)
        if not math.isclose(half_points*step, args.xi_max, rel_tol=1e-12, abs_tol=1e-12):
            parser.error("window endpoint must be a step multiple")
        xi = np.arange(-half_points, half_points + 1)*step
        kernel, prime_count = SOURCE.prime_kernel(xi, 2*max(width*width for width, _ in families))
        if prime_count != 41136:
            raise ValueError("support-derived prime-power count guard failed")
        references = {}
        for order in (256, 512):
            reference = np.column_stack([direct.reference_transform(xi, families, vector, 24, order)
                                         for vector in (base, correction)])
            references[order] = reference
        reference_controls.append({"xi_step": step,
            "base_max_movement": float(np.max(np.abs(references[256][:, 0]-references[512][:, 0]))),
            "corr_max_movement": float(np.max(np.abs(references[256][:, 1]-references[512][:, 1])))})
        reference_functionals = {order: direct.functional(xi, values[:, 0], values[:, 1], kernel)
                                for order, values in references.items()}
        baseline = np.column_stack([SOURCE.filon_transform(xi, families, vector, 24, 4)
                                    for vector in (base, correction)])
        baseline_functional = direct.functional(xi, baseline[:, 0], baseline[:, 1], kernel)
        baseline_difference = float(np.trapezoid(reference_functionals[512]-baseline_functional, xi))
        prior = next((row for row in old["rows"] if row["xi_step"] == step and row["xi_max"] == args.xi_max
                      and row["panels"] == 24 and row["degree"] == 4 and row["nodes_per_panel"] == 512), None)
        baseline_control = {"xi_step": step, "same_run_signed_difference": baseline_difference,
                            "historical_row_available": prior is not None}
        if prior is not None:
            relative = abs(baseline_difference-prior["direct_signed_difference"])/max(abs(prior["direct_signed_difference"]), 1)
            baseline_control["relative_movement"] = relative
            if relative > 1e-10:
                raise ArithmeticError("2295 same-run baseline control failed")
        baseline_controls.append(baseline_control)
        for panels, degree in profiles:
            candidate = separated_transform(xi, families, coefficients, panels, degree)
            functional = direct.functional(xi, candidate[:, 0], candidate[:, 1], kernel)
            for order in (256, 512):
                difference = reference_functionals[order]-functional
                signed = float(np.trapezoid(difference, xi))
                rows.append({"xi_step": step, "xi_max": args.xi_max, "xi_points": len(xi),
                             "panels": panels, "degree": degree, "reference_order": order,
                             "reference_signed_integral": float(np.trapezoid(reference_functionals[order], xi)),
                             "candidate_signed_integral": float(np.trapezoid(functional, xi)),
                             "direct_signed_difference": signed,
                             "direct_absolute_difference": float(np.trapezoid(np.abs(difference), xi)),
                             "base_max_difference": float(np.max(np.abs(references[order][:, 0]-candidate[:, 0]))),
                             "corr_max_difference": float(np.max(np.abs(references[order][:, 1]-candidate[:, 1]))),
                             "sampled_budget_ratio": abs(signed)/1e7,
                             "sampled_budget_pass": abs(signed) <= 1e7})
    profile_summaries = []
    for panels, degree in profiles:
        profile_rows = [row for row in rows if row["panels"] == panels and row["degree"] == degree]
        profile_summaries.append({"panels": panels, "degree": degree,
            "max_sampled_signed_budget_ratio": max(row["sampled_budget_ratio"] for row in profile_rows),
            "max_sampled_absolute_budget_ratio": max(row["direct_absolute_difference"]/1e7 for row in profile_rows),
            "signed_diagnostic_pass_all_controls": all(row["sampled_budget_pass"] for row in profile_rows),
            "absolute_diagnostic_pass_all_controls": all(row["direct_absolute_difference"] <= 1e7 for row in profile_rows)})
    result = {"record": 2296, "status": "CARRIER-SEPARATED-FUNCTIONAL-SCREEN",
              "certificate": False, "hgap_closed": False, "diagnostic_budget": 10000000,
              "owner": {"family_count": len(families), "carrier_count": len(carrier_groups(families)),
                        "prime_power_count": 41136, "base_md5": capture["owner_capture"]["base_md5"],
                        "corr_md5": capture["owner_capture"]["corr_md5"]},
              "identity_control": control, "reference_controls": reference_controls,
              "baseline_controls": baseline_controls, "rows": rows,
              "profile_summaries": profile_summaries,
              "source_sha256": {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (SOURCE.CAPTURE, Path(SOURCE.__file__), Path(direct.__file__), Path(__file__))},
              "nonclaims": ["numerical reference, not a truth oracle",
                            "same-rule reference order agreement is not independent analytic validation",
                            "sampled signed budget pass is not an absolute error certificate",
                            "carrier-group rounding and interpolation remainder remain unpriced",
                            "no ideal-to-discrete bridge, selected-owner readback or infinite-tail bound",
                            "no hgap supplier, producer GO or RH claim"]}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({"identity_control": control, "baseline_controls": baseline_controls}))
    for row in rows:
        if row["reference_order"] == 512:
            print(json.dumps({key: row[key] for key in ("xi_step", "panels", "degree", "direct_signed_difference",
                                                      "direct_absolute_difference", "sampled_budget_ratio")}))


if __name__ == "__main__":
    main()
