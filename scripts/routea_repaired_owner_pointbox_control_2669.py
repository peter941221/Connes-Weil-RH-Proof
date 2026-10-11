"""Independent point-box control for the repaired 2338 owner.

The 2242 evaluator returns a binary64 hull for the four functions
F, F'', G, G''.  This control reconstructs the repaired coefficient midpoint
casts used by record 2668, evaluates the same finite-family formula with exact
binary64 operands at high mpmath precision, and checks containment at a
5001-point grid.  It is a sampled control, not a continuum theorem or a Lean
certificate.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
EVALUATOR = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
STRIP = ROOT / "scripts/routea_corrected_strip_envelope_2303.py"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
REPAIR_REREAD = ROOT / "results/2665_l1_margin_repair.json"
OUTPUT = ROOT / "results/2669_repaired_owner_pointbox_control.json"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_float(value: float) -> mp.mpf:
    numerator, denominator = value.as_integer_ratio()
    return mp.mpf(numerator) / mp.mpf(denominator)


def exact_mp(value) -> mp.mpf:
    if isinstance(value, Fraction):
        return mp.mpf(value.numerator) / mp.mpf(value.denominator)
    return exact_float(float(value))


def exact_corrected_fam(raw_families):
    return [(Fraction.from_float(float(width)) ** 2, theta)
            for width, theta in raw_families]


def coefficient_arrays(rows):
    base = []
    correction = []
    for row in rows:
        pair = []
        for name in ("ideal_base_coefficient", "ideal_correction_coefficient"):
            components = {}
            for part in ("real", "imag"):
                ball = row[name][part]
                midpoint = (Fraction(ball["lower_exact"]) +
                            Fraction(ball["upper_exact"])) / 2
                components[part] = float(midpoint)
            pair.append(complex(components["real"], components["imag"]))
        base.append(pair[0])
        correction.append(pair[1])
    return np.asarray(base, dtype=complex), np.asarray(correction, dtype=complex)


def md5_complex(values) -> str:
    return hashlib.md5(np.ascontiguousarray(values, dtype=complex).tobytes()).hexdigest()


def install_exact_squared_radius(interval, rec, width: float, channel_order: int):
    numerator, denominator = width.as_integer_ratio()
    if (denominator & (denominator - 1) or
            numerator.bit_length() * 2 > rec["a"].x.prec):
        raise AssertionError("stored width square is not exact at the MPFR precision")
    width_mp = interval.M()
    t120 = interval.mk(-120.0)
    try:
        width_mp.set_d(width)
        interval.MUL(interval.BR(rec["a"].x), interval.BR(width_mp.x),
                     interval.BR(width_mp.x), interval.RNDN)
        radius_sq_lo, radius_sq_hi = interval.M(), interval.M()
        try:
            interval.MUL(interval.BR(radius_sq_lo.x), interval.BR(rec["a"].x),
                         interval.BR(rec["a"].x), interval.RNDD)
            interval.MUL(interval.BR(radius_sq_hi.x), interval.BR(rec["a"].x),
                         interval.BR(rec["a"].x), interval.RNDU)
            interval.DIV(interval.BR(rec["s2a2_lo"].x),
                         interval.BR(interval.SIXTY.x),
                         interval.BR(radius_sq_hi.x), interval.RNDD)
            interval.DIV(interval.BR(rec["s2a2_hi"].x),
                         interval.BR(interval.SIXTY.x),
                         interval.BR(radius_sq_lo.x), interval.RNDU)
        finally:
            radius_sq_lo.clear()
            radius_sq_hi.clear()
        interval.DIV(interval.BR(rec["inv_d"].x), interval.BR(interval.ONE.x),
                     interval.BR(rec["a"].x), interval.RNDD)
        interval.DIV(interval.BR(rec["inv_u"].x), interval.BR(interval.ONE.x),
                     interval.BR(rec["a"].x), interval.RNDU)
        if channel_order == 2:
            mr_lo, mr_hi = interval.M(), interval.M()
            try:
                interval.MUL(interval.BR(mr_lo.x), interval.BR(t120.x),
                             interval.BR(rec["th"].x), interval.RNDD)
                interval.MUL(interval.BR(mr_hi.x), interval.BR(t120.x),
                             interval.BR(rec["th"].x), interval.RNDU)
                interval.DIV(interval.BR(rec["fq_lo"].x), interval.BR(mr_lo.x),
                             interval.BR(rec["a"].x), interval.RNDD)
                interval.DIV(interval.BR(rec["fq_hi"].x), interval.BR(mr_hi.x),
                             interval.BR(rec["a"].x), interval.RNDU)
            finally:
                mr_lo.clear()
                mr_hi.clear()
    finally:
        width_mp.clear()
        t120.clear()


def configure_exact_squared_radii(interval, kernel, raw_families, coefficients):
    rec_index = 0
    for (width, _theta), coefficient in zip(raw_families, coefficients):
        if float(complex(coefficient).real) == 0.0 and \
                float(complex(coefficient).imag) == 0.0:
            continue
        install_exact_squared_radius(interval, kernel.recs[rec_index],
                                     float(width), kernel.k)
        rec_index += 1
    if rec_index != len(kernel.recs):
        raise AssertionError("kernel records do not match nonzero coefficient families")


def audit_radius_rounding(raw_families) -> dict:
    nearest_differences = []
    for width, _theta in raw_families:
        exact_radius = Fraction.from_float(float(width)) ** 2
        nearest_radius = float(width) * float(width)
        nearest_differences.append(Fraction.from_float(nearest_radius) - exact_radius)
    nearest_under = [gap for gap in nearest_differences if gap < 0]
    exact_support = max(Fraction.from_float(float(width)) ** 2
                        for width, _theta in raw_families)
    outward_support = math.nextafter(float(exact_support), math.inf)
    support_gap = Fraction.from_float(outward_support) - exact_support
    return {
        "radius_construction": "exact binary64 width squared in 256-bit MPFR",
        "nearest_product_underrounded_family_radius_count": len(nearest_under),
        "underrounded_family_radius_count": 0,
        "max_nearest_product_radius_shortfall_exact": str(max(-gap for gap in nearest_under)
                                                           if nearest_under else Fraction(0)),
        "mpfr_radius_matches_exact_width_square": True,
        "mpfr_precision_bits": 256,
        "exact_squared_radii_configured": len(raw_families),
        "outward_support_radius": outward_support,
        "exact_support_radius_from_binary64_widths": str(exact_support),
        "outward_support_radius_gap_exact": str(support_gap),
        "outward_support_covers_exact_owner_support": support_gap >= 0,
    }


def reference_value(families, coefficients, order: int, x: float) -> mp.mpc:
    """Evaluate the exact stored-width-squared formula without reusing the hull."""
    xx = exact_float(x)
    total = mp.mpc(0)
    for (radius_raw, theta_raw), coefficient in zip(families, coefficients):
        radius = exact_mp(radius_raw)
        theta = exact_float(theta_raw)
        u = xx / radius
        q = 1 - u * u
        if q <= 0:
            continue
        phi = mp.exp(-30 / q)
        e1 = -(60 / radius) * u / (q * q)
        if order == 0:
            factor = 1
        else:
            e2 = -(60 / (radius * radius)) * (
                1 / (q * q) + 4 * u * u / (q ** 3))
            factor = e2 + (e1 + 1j * theta) ** 2
        c = exact_float(complex(coefficient).real) + 1j * exact_float(
            complex(coefficient).imag)
        total += c * phi * mp.exp(1j * theta * xx) * factor
    return total


def run(nodes: int = 5001, dps: int = 90,
        output: Path = OUTPUT) -> dict:
    if nodes < 3 or nodes % 2 == 0:
        raise ValueError("nodes must be odd and at least three")
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    reread = json.loads(REPAIR_REREAD.read_text(encoding="utf-8"))
    base, correction = coefficient_arrays(repair["coefficient_rows"])
    repaired_hashes = {"base": md5_complex(base),
                       "correction": md5_complex(correction)}
    expected_hashes = {"base": reread["treatment"]["base_md5"],
                       "correction": reread["treatment"]["corr_md5"]}
    if repaired_hashes != expected_hashes:
        raise AssertionError("reconstructed repair arrays differ from record 2665")
    captured_hashes = {"base": capture["base_md5"],
                       "correction": capture["corr_md5"]}
    if repaired_hashes == captured_hashes:
        raise AssertionError("repair arrays unexpectedly equal captured owner")

    evaluator = load("evaluator2669", EVALUATOR)
    strip = load("strip2669", STRIP)
    raw_families, _, _, _ = strip.load_owner()
    exact_families = exact_corrected_fam(raw_families)
    radius_audit = audit_radius_rounding(raw_families)
    families = raw_families
    channels = [
        (evaluator.Kernel(families, base, 0), base, 0, "base_M0"),
        (evaluator.Kernel(families, base, 2), base, 2, "base_D2"),
        (evaluator.Kernel(families, correction, 0), correction, 0, "corr_M0"),
        (evaluator.Kernel(families, correction, 2), correction, 2, "corr_D2"),
    ]
    for kernel, coefficients, _order, _name in channels:
        configure_exact_squared_radii(evaluator, kernel, families, coefficients)
    radius = radius_audit["outward_support_radius"]
    grid = np.linspace(-radius, radius, nodes)
    points = set(map(float, grid))
    for family_radius, _theta in families:
        family_radius = float(family_radius)
        for endpoint in (-family_radius, family_radius):
            points.add(endpoint)
            points.add(float(np.nextafter(endpoint, -np.inf)))
            points.add(float(np.nextafter(endpoint, np.inf)))
    points = sorted(points)
    failures = []
    worst = mp.mpf(0)
    worst_row = None
    checked = 0
    corner_norm_underestimates = 0
    corner_term_input_underestimates = 0
    point_term_input_underestimates = 0
    point_term_input_underestimates_beyond_mpfr_rounding = 0
    max_corner_norm_shortfall = mp.mpf(0)
    max_corner_term_shortfall = mp.mpf(0)
    max_point_term_shortfall = mp.mpf(0)
    sigma = -0.5
    exact_sigma = exact_float(sigma)
    with mp.workdps(dps):
        for index, point in enumerate(points):
            exact_x = exact_float(float(point))
            exact_exp = mp.exp(exact_sigma * exact_x)
            factor = math.exp(sigma * float(point))
            geometry_cache = [None] * len(channels[0][0].recs)
            for channel_index, (kernel, coefficients, order, name) in enumerate(channels):
                if channel_index == 0:
                    geometry_cache = [None] * len(kernel.recs)
                _ok, bounds, _floor = kernel.eval_box(
                    float(point), float(point), geometry_cache)
                value = reference_value(exact_families, coefficients, order,
                                        float(point))
                re, im = mp.re(value), mp.im(value)
                rlo, rhi, ilo, ihi = map(mp.mpf, bounds)
                violation = max(mp.mpf(0), rlo - re, re - rhi,
                                ilo - im, im - ihi)
                scale = max(mp.mpf(1), abs(re), abs(im), abs(rlo),
                            abs(rhi), abs(ilo), abs(ihi))
                relative = violation / scale
                checked += 1
                if relative > worst:
                    worst = relative
                    worst_row = [index, float(point), name, str(violation)]
                if violation > 0 and len(failures) < 8:
                    failures.append({
                        "index": index,
                        "point": float(point),
                        "channel": name,
                        "violation": str(violation),
                        "reference_re": str(re),
                        "reference_im": str(im),
                        "bounds": [str(rlo), str(rhi), str(ilo), str(ihi)],
                    })
                rmax = max(abs(bounds[0]), abs(bounds[1]))
                imax = max(abs(bounds[2]), abs(bounds[3]))
                corner_norm = mp.sqrt(exact_float(rmax) ** 2 +
                                      exact_float(imax) ** 2)
                rounded_norm = math.hypot(rmax, imax)
                corner_norm_shortfall = corner_norm - exact_float(rounded_norm)
                if corner_norm_shortfall > 0:
                    corner_norm_underestimates += 1
                    max_corner_norm_shortfall = max(
                        max_corner_norm_shortfall, corner_norm_shortfall)
                cell_weight = 0.5 if index == 0 or index == len(points) - 1 else 1.0
                rounded_input_product = (exact_float(rounded_norm) *
                                         exact_float(cell_weight) *
                                         exact_float(factor))
                corner_target = corner_norm * exact_float(cell_weight) * exact_exp
                point_target = abs(value) * exact_float(cell_weight) * exact_exp
                corner_shortfall = corner_target - rounded_input_product
                point_shortfall = point_target - rounded_input_product
                if corner_shortfall > 0:
                    corner_term_input_underestimates += 1
                    max_corner_term_shortfall = max(
                        max_corner_term_shortfall, corner_shortfall)
                if point_shortfall > 0:
                    point_term_input_underestimates += 1
                    max_point_term_shortfall = max(max_point_term_shortfall,
                                                   point_shortfall)
                    if point_shortfall > max(mp.mpf(1), point_target) * mp.power(2, -200):
                        point_term_input_underestimates_beyond_mpfr_rounding += 1

    result = {
        "record": 2669,
        "status": (f"REPAIRED_OWNER_POINTBOX_{nodes}_CONTROL_PASS"
                    if not failures else
                    f"REPAIRED_OWNER_POINTBOX_{nodes}_CONTROL_FAIL"),
        "evaluator": "scripts/routea_weighted_zero_zero_count_certificate_2242.py",
        "strip": "scripts/routea_corrected_strip_envelope_2303.py",
        "repair_source": "results/2338_exact_interpolation_repair.json",
        "owner_source": "2338 exact-interpolation coefficient-ball midpoints cast to binary64",
        "nodes": nodes,
        "uniform_grid_points": nodes,
        "distinct_points_including_support_boundaries": len(points),
        "support_boundary_added_points": len(points) - nodes,
        "channels": len(channels),
        "checked_point_channel_values": checked,
        "mpmath_dps": dps,
        "public_hull_ulp_margin": evaluator.PUBLIC_HULL_ULPS,
        "stored_operands_converted_exactly": True,
        "repaired_coefficient_md5": repaired_hashes,
        "captured_coefficient_md5": captured_hashes,
        "repair_arrays_match_2665_treatment": True,
        "source_sha256": sha256(EVALUATOR),
        "control_script_sha256": sha256(Path(__file__)),
        "strip_source_sha256": sha256(STRIP),
        "repair_artifact_sha256": sha256(REPAIR),
        "containment_failures_recorded": len(failures),
        "first_failures": failures,
        "worst_relative_violation": float(worst),
        "worst_row": worst_row,
        "support_boundary_probe_included": True,
        "radius_audit": radius_audit,
        "sigma": sigma,
        "nearest_binary64_hypot_underestimates_box_corner_count":
            corner_norm_underestimates,
        "nearest_binary64_weighted_input_underestimates_box_corner_count":
            corner_term_input_underestimates,
        "nearest_binary64_weighted_input_underestimates_point_value_count":
            point_term_input_underestimates,
        "point_input_underestimates_beyond_2^-200_rounding_count":
            point_term_input_underestimates_beyond_mpfr_rounding,
        "max_box_corner_norm_shortfall": str(max_corner_norm_shortfall),
        "max_box_corner_weighted_input_shortfall": str(max_corner_term_shortfall),
        "max_actual_point_weighted_input_shortfall": str(max_point_term_shortfall),
        "continuum_enclosure_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=5001)
    parser.add_argument("--dps", type=int, default=90)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    run(args.nodes, args.dps, args.output)
