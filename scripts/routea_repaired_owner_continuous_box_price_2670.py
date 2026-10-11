"""Price a direct continuous box enclosure for the repaired owner.

Each cell is bounded by the 2242 interval evaluator. MPFR directed rounding
then prices cell width * sup(|channel|) * sup(exp(sigma*x)). This is a numeric
design probe, not a Lean-imported certificate or a producer theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
REPAIR_REREAD = ROOT / "results/2665_l1_margin_repair.json"
NODE_CONTROL = ROOT / "results/2668_repaired_owner_fullgrid.json"
OUTPUT = ROOT / "results/2670_repaired_owner_continuous_box_price.json"
KNOWN_ERROR_2109_DECIMAL = "74601530.30234718"
KNOWN_ERROR_2109 = float(KNOWN_ERROR_2109_DECIMAL)


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficient_arrays(rows):
    base = []
    correction = []
    for row in rows:
        arrays = []
        for name in ("ideal_base_coefficient", "ideal_correction_coefficient"):
            components = {}
            for part in ("real", "imag"):
                ball = row[name][part]
                midpoint = (Fraction(ball["lower_exact"]) +
                            Fraction(ball["upper_exact"])) / 2
                components[part] = float(midpoint)
            arrays.append(complex(components["real"], components["imag"]))
        base.append(arrays[0])
        correction.append(arrays[1])
    return base, correction


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


def make_channels(interval, families, base, correction):
    return [
        interval.Kernel(families, base, 0),
        interval.Kernel(families, base, 2),
        interval.Kernel(families, correction, 0),
        interval.Kernel(families, correction, 2),
    ]


def price_partition(interval, channels, radius: float, cells: int,
                     sigma: float) -> dict:
    grid = np.linspace(-radius, radius, cells + 1)
    lo_m, hi_m, width_m = interval.M(), interval.M(), interval.M()
    rmax_m, imax_m = interval.M(), interval.M()
    square_r, square_i = interval.M(), interval.M()
    norm_square, norm = interval.M(), interval.M()
    sigma_m, endpoint_m = interval.M(), interval.M()
    exponent, weight = interval.M(), interval.M()
    term, total = interval.M(), interval.M()
    channel_totals = [interval.M() for _ in channels]
    objects = [lo_m, hi_m, width_m, rmax_m, imax_m, square_r, square_i,
               norm_square, norm, sigma_m, endpoint_m, exponent, weight,
               term, total, *channel_totals]
    for value in objects:
        value.set_d(0.0)
    sigma_m.set_d(sigma)
    box_count = 0
    max_box_width = 0.0

    try:
        for cell_index in range(cells):
            xlo = float(grid[cell_index])
            xhi = float(grid[cell_index + 1])
            lo_m.set_d(xlo)
            hi_m.set_d(xhi)
            interval.SUB(interval.BR(width_m.x), interval.BR(hi_m.x),
                         interval.BR(lo_m.x), interval.RNDU)
            max_box_width = max(max_box_width,
                                width_m.get_d(interval.RNDU))
            # The exponential is monotone, so its maximum is at one endpoint.
            weighted_endpoint = xhi if sigma >= 0.0 else xlo
            endpoint_m.set_d(weighted_endpoint)
            interval.MUL(interval.BR(exponent.x), interval.BR(sigma_m.x),
                         interval.BR(endpoint_m.x), interval.RNDU)
            interval.EXP(interval.BR(weight.x), interval.BR(exponent.x),
                          interval.RNDU)

            for channel_index, kernel in enumerate(channels):
                _no_zero, bounds, _floor = kernel.eval_box(xlo, xhi)
                rlo, rhi, ilo, ihi = bounds
                rmax_m.set_d(max(abs(rlo), abs(rhi)))
                imax_m.set_d(max(abs(ilo), abs(ihi)))
                interval.MUL(interval.BR(square_r.x), interval.BR(rmax_m.x),
                             interval.BR(rmax_m.x), interval.RNDU)
                interval.MUL(interval.BR(square_i.x), interval.BR(imax_m.x),
                             interval.BR(imax_m.x), interval.RNDU)
                interval.ADD(interval.BR(norm_square.x),
                             interval.BR(square_r.x), interval.BR(square_i.x),
                             interval.RNDU)
                interval.SQRT(interval.BR(norm.x),
                              interval.BR(norm_square.x), interval.RNDU)
                interval.MUL(interval.BR(term.x), interval.BR(width_m.x),
                             interval.BR(norm.x), interval.RNDU)
                interval.MUL(interval.BR(term.x), interval.BR(term.x),
                             interval.BR(weight.x), interval.RNDU)
                interval.ADD(interval.BR(channel_totals[channel_index].x),
                             interval.BR(channel_totals[channel_index].x),
                             interval.BR(term.x), interval.RNDU)
                interval.ADD(interval.BR(total.x), interval.BR(total.x),
                             interval.BR(term.x), interval.RNDU)
                box_count += 1

        channel_upper = [value.get_d(interval.RNDU)
                         for value in channel_totals]
        total_upper = total.get_d(interval.RNDU)
        total_upper_exact = Fraction.from_float(total_upper)
        budget_exact = Fraction(KNOWN_ERROR_2109_DECIMAL)
        return {
            "cells": cells,
            "channel_box_evaluations": box_count,
            "max_cell_width_upper": max_box_width,
            "channel_integral_upper": channel_upper,
            "total_integral_upper": total_upper,
            "budget": KNOWN_ERROR_2109,
            "budget_exact_decimal": KNOWN_ERROR_2109_DECIMAL,
            "budget_ratio": float(total_upper_exact / budget_exact),
            "below_knownError2109": total_upper_exact <= budget_exact,
        }
    finally:
        for value in objects:
            value.clear()


def run(cell_counts: list[int], sigma: float) -> dict:
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    reread = json.loads(REPAIR_REREAD.read_text(encoding="utf-8"))
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    base, correction = coefficient_arrays(repair["coefficient_rows"])
    hashes = {"base": md5_complex(base), "correction": md5_complex(correction)}
    expected = {"base": reread["treatment"]["base_md5"],
                "correction": reread["treatment"]["corr_md5"]}
    captured = {"base": capture["base_md5"],
                "correction": capture["corr_md5"]}
    if hashes != expected or hashes == captured:
        raise AssertionError("owner arrays do not match the repaired treatment")

    interval = load("interval2670", ROOT / "scripts" /
                    "routea_weighted_zero_zero_count_certificate_2242.py")
    strip = load("strip2670", ROOT / "scripts" /
                 "routea_corrected_strip_envelope_2303.py")
    raw_families, _base_capture, _correction_capture, _anchors = strip.load_owner()
    families = raw_families
    radius_audit = audit_radius_rounding(raw_families)
    support_radius = radius_audit["outward_support_radius"]
    channels = make_channels(interval, families, base, correction)
    for kernel, coefficients in zip(channels,
                                   (base, base, correction, correction)):
        configure_exact_squared_radii(interval, kernel, families, coefficients)
    rows = [price_partition(interval, channels, support_radius, cells, sigma)
            for cells in cell_counts]

    node_control = json.loads(NODE_CONTROL.read_text(encoding="utf-8"))
    return {
        "record": 2670,
        "status": "CONTINUOUS_BOX_PRICE_PROBE_NOT_CERTIFICATE",
        "owner_source": "2338 exact-interpolation coefficient-ball midpoints cast to binary64",
        "repaired_coefficient_md5": hashes,
        "captured_coefficient_md5": captured,
        "support_radius": support_radius,
        "radius_audit": radius_audit,
        "price_scope": "exact storedWidth-squared radii represented exactly in 256-bit MPFR",
        "sigma": sigma,
        "knownError2109": KNOWN_ERROR_2109,
        "knownError2109_exact_decimal": KNOWN_ERROR_2109_DECIMAL,
        "partitions": rows,
        "node_control_record": 2668,
        "node_control_total": sum(node_control["directed_term_binary64_roundup_integrals"]),
        "node_control_total_source_status": node_control["status"],
        "cell_bound_method": (
            "2242 natural interval hull; MPFR RNDU for rectangle modulus, "
            "monotone exponential, cell width, products, and accumulation"),
        "source_sha256": {
            "script": sha256(Path(__file__)),
            "interval_evaluator": sha256(ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"),
            "strip_owner": sha256(ROOT / "scripts/routea_corrected_strip_envelope_2303.py"),
            "repair_artifact": sha256(REPAIR),
            "node_control": sha256(NODE_CONTROL),
        },
        "continuum_enclosure_proved": False,
        "lean_numeric_imported": False,
        "actual_owner_identity_proved": False,
        "infinite_xi_tail_closed": False,
        "producer_go": False,
        "rh_claim": False,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", default="256,1024,4096")
    parser.add_argument("--sigma", type=float, default=-0.5)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    cell_counts = [int(value) for value in args.cells.split(",")]
    if not cell_counts or any(value < 1 for value in cell_counts):
        raise ValueError("cell counts must be positive")
    result = run(cell_counts, args.sigma)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps({"record": result["record"], "status": result["status"],
                      "support_radius": result["support_radius"],
                      "partitions": result["partitions"]}, indent=2))


if __name__ == "__main__":
    main()
