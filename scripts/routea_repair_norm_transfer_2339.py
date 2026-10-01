"""2339: additive norm transfer and integrable n=0 Fourier repair bound."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
import routea_marked_sign_arb_certificate_2337 as certificate

ROOT = Path(__file__).resolve().parents[1]
INPUT_HASHES = {
    "results/2275_gap_owner_audit.json": "743fe372bef89b5730c38274d5a5517ac9ea4d3421989d46c49d4af3e78b5e74",
    "results/2303_corrected_strip_envelope.json": "12fbe54b1eb53565ec730765ac56054742791bf61ea7a9eecff5e3825f45d35b",
    "results/2338_exact_interpolation_repair.json": "7efde152db5e18c2d312cae16309172154044b443477bca75b9619b3070eb258",
    "scripts/routea_exact_interpolation_repair_2338.py": "c24a13fa76af8c66b10e8d3d034d55e3e799319d1d1f6645b0efdd4e02990c64",
    "scripts/routea_marked_sign_arb_certificate_2337.py": "67b7057d850c35dd74772b320e8198da4eba6661dae30254e1cf78761346715a",
}
PIN = Fraction("2644542.8515")
lift = certificate.lift_fraction


def check_hash(path, expected):
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"upstream hash mismatch: {path.name}")
    return actual


def endpoint(value):
    return certificate.serialize_real(value.upper())


def delta_upper(row, channel):
    bounds = row[channel + "_delta_abs"]
    lower, upper = (Fraction(bounds[key]) for key in ("lower_exact", "upper_exact"))
    if not 0 <= lower <= upper:
        raise ValueError("invalid nonnegative coefficient delta interval")
    return lift(upper).upper()


def profile_bounds():
    scale = arb(-30).exp()
    return [scale, 60 * scale, 3900 * scale, 272160 * scale]


def moment_charges(radius, old_radius, theta, coef_abs, delta_abs, sigma):
    if not radius > 0 or not old_radius > 0:
        raise ValueError("positive radii required")
    bound0, bound1, bound2, bound3 = profile_bounds()
    theta = abs(theta)
    repair_terms = [bound0, bound1 / radius + theta * bound0,
                    bound2 / radius**2 + 2 * theta * bound1 / radius + theta**2 * bound0]
    repair_scale = delta_abs * 2 * radius * (abs(sigma) * radius).exp()
    low, high = min(radius, old_radius), max(radius, old_radius)
    geometry_terms = [bound1 / low,
                      (bound1 + bound2) / low**2 + theta * bound1 / low,
                      (2 * bound2 + bound3) / low**3
                      + 2 * theta * (bound1 + bound2) / low**2 + theta**2 * bound1 / low]
    geometry_scale = coef_abs * abs(radius - old_radius) * 2 * high * (abs(sigma) * high).exp()
    return ([repair_scale * term for term in repair_terms],
            [geometry_scale * term for term in geometry_terms])


def first_norm(norm0, norm2, sigma, step=Fraction(1, 10)):
    if not step > 0:
        raise ValueError("positive finite-difference step required")
    step = lift(step)
    growth = (abs(sigma) * step).exp()
    return ((1 + growth) * norm0 / step + step * growth * norm2 / 2).upper()


def decay_pair(norm0, norm1, norm2, sigma):
    return [norm0.upper(), (norm2 + 2 * abs(sigma) * norm1 + sigma**2 * norm0).upper()]


def envelope(pair, frequency):
    frequency = abs(frequency)
    return pair[0] if frequency.is_zero() else min(pair[0], (pair[1] / frequency**2).upper())


def square_change(pairs, frequency):
    base, corr, base_error, corr_error = [envelope(pair, frequency) for pair in pairs]
    product = base * corr
    difference = base_error * corr + base * corr_error + base_error * corr_error
    return (difference * (2 * product + difference)).upper()


def tail_numerator(pairs):
    base, corr, base_error, corr_error = [pair[1] for pair in pairs]
    product = base * corr
    difference = base_error * corr + base * corr_error + base_error * corr_error
    return (difference * (2 * product + difference)).upper()


def full_line_charge(pairs):
    boundaries = [Fraction(0)] + [Fraction(2)**power for power in range(-4, 17)]
    central, bins = arb(0), []
    for left, right in zip(boundaries, boundaries[1:]):
        charge = lift(right - left) * square_change(pairs, lift(left)) / arb.pi()
        central += charge
        bins.append({"left_t_exact": str(left), "right_t_exact": str(right),
                     "two_sided_charge_upper": endpoint(charge)})
    numerator = tail_numerator(pairs)
    tail = numerator / (7 * arb.pi() * lift(boundaries[-1])**7)
    return {"central_upper": endpoint(central), "tail_upper": endpoint(tail),
            "total_upper": endpoint(central + tail), "tail_t_cutoff_exact": str(boundaries[-1]),
            "tail_numerator_upper": endpoint(numerator), "bins": bins}


def run_transfer():
    ctx.prec = 320
    hashes = {name: check_hash(ROOT / name, expected) for name, expected in INPUT_HASHES.items()}
    capture, families, coefficients, _, _ = certificate.load_capture()
    repair = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())
    baseline = json.loads((ROOT / "results/2303_corrected_strip_envelope.json").read_text())
    if (repair["capture_sha256"] != hashes["results/2275_gap_owner_audit.json"]
            or repair["solve_algorithm"] != "precond"
            or not repair["solution_interval_residual_contains_zero"]
            or baseline["status"] != "CORRECTED-STRIP-COVERED"):
        raise ValueError("upstream certificate status mismatch")
    coef_rows = repair["coefficient_rows"]
    if [row["index"] for row in coef_rows] != list(range(30)):
        raise ValueError("coefficient row order mismatch")
    if [row["j"] for row in baseline["grid_rows"]] != list(range(-50, 51)):
        raise ValueError("strip row order mismatch")
    radii = [width * width for width, _ in families]
    old_radii = [certificate.lift_float(float.fromhex(width)**2) for width, _ in capture["families_hex"]]
    max_radius = max(radii + old_radii)
    rows, decay_inputs = [], None
    for source in baseline["grid_rows"]:
        sigma = lift(Fraction(source["j"], 100))
        growth = (abs(sigma - certificate.lift_float(source["sigma"])) * max_radius).exp()
        channels, ideal_norms, decay_channels = {}, [], []
        for channel_index, channel in enumerate(("base", "correction")):
            delta, geometry = [arb(0)] * 3, [arb(0)] * 3
            for index, (_, theta) in enumerate(families):
                delta_terms, geom_terms = moment_charges(
                    radii[index], old_radii[index], theta, abs(coefficients[channel_index][index]).upper(),
                    delta_upper(coef_rows[index], channel), sigma)
                delta = [old + new for old, new in zip(delta, delta_terms)]
                geometry = [old + new for old, new in zip(geometry, geom_terms)]
            prefix = "base" if channel == "base" else "corr"
            stored0 = (certificate.lift_float(source["norms"][prefix + "_M0"]) * growth + geometry[0]).upper()
            stored2 = (certificate.lift_float(source["norms"][prefix + "_D2"]) * growth + geometry[2]).upper()
            ideal0, ideal2 = (stored0 + delta[0]).upper(), (stored2 + delta[2]).upper()
            channels[channel] = {"repair_moments_upper": [endpoint(value) for value in delta],
                                 "radius_geometry_moments_upper": [endpoint(value) for value in geometry],
                                 "stored_norm0_upper": endpoint(stored0), "stored_norm2_upper": endpoint(stored2),
                                 "ideal_norm0_upper": endpoint(ideal0), "ideal_norm2_upper": endpoint(ideal2)}
            ideal_norms.append((ideal0, ideal2))
            decay_channels.append((decay_pair(stored0, first_norm(stored0, stored2, sigma), stored2, sigma),
                                   decay_pair(*delta, sigma)))
        bound = min((ideal_norms[0][1] * ideal_norms[1][0]).upper(),
                    (ideal_norms[1][1] * ideal_norms[0][0]).upper())
        rows.append({"j": source["j"], "sigma_exact": str(Fraction(source["j"], 100)),
                     "weight_rounding_factor_upper": endpoint(growth), "channels": channels,
                     "min_product_upper": endpoint(bound), "fits_existing_pin": bool(bound <= lift(PIN)),
                     "sufficient_bound_excess_upper": endpoint(bound - lift(PIN))})
        if source["j"] == 50:
            decay_inputs = [decay_channels[0][0], decay_channels[1][0], decay_channels[0][1], decay_channels[1][1]]
    maximum = max(rows, key=lambda row: Fraction(row["min_product_upper"]["upper_exact"]))
    failures = [row["j"] for row in rows if not row["fits_existing_pin"]]
    return {"record": 2339, "status": "ADDITIVE_NORM_AND_INTEGRABLE_REPAIR_BOUND_ONLY",
            "precision_bits": ctx.prec, "input_sha256": hashes,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "baseline_policy": "full published 2303 norms; no reserve subtraction",
            "bound_depends_on_2303_certificate": True, "upstream_reintegrated": False,
            "radius_rounding_nonzero_count": sum(not (radius - old).is_zero() for radius, old in zip(radii, old_radii)),
            "rows": rows, "existing_pin_exact": str(PIN), "all_nodes_fit_existing_pin": not failures,
            "failed_sufficient_bound_nodes": failures, "maximum_node": maximum["j"],
            "maximum_min_product_upper": maximum["min_product_upper"],
            "fourier_scope": "n=0, integral over all xi of abs(|B1 C1|^2-|B0 C0|^2)",
            "fourier_frequency_convention": "t=-2*pi*xi; both signs charged by 1/pi",
            "decay_pairs": [[endpoint(value) for value in pair] for pair in decay_inputs],
            "fourier_unweighted_change": full_line_charge(decay_inputs),
            "signed_kernel_repair_charge_priced": False, "lean_imported_certificate": False,
            "owner_transfer_to_live_consumer": False, "healthy_detector_instantiated": False,
            "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2339_repair_norm_transfer.json")
    args = parser.parse_args()
    result = run_transfer()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("all_nodes_fit_existing_pin", result["all_nodes_fit_existing_pin"], "failed_nodes", result["failed_sufficient_bound_nodes"])
    print("max", result["maximum_min_product_upper"]["display"])
    print("unweighted_full_line_upper", result["fourier_unweighted_change"]["total_upper"]["display"])
