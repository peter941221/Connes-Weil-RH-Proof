"""Export one reproducible, outward-rounded cell-price certificate.

The evaluator rectangle is inherited from record 2242. This exporter records
its final binary64 endpoints and independently rebuilds the scalar price with
an upward binary64 conversion after every MPFR operation. The result is a
checkable arithmetic certificate, not a proof that the 2242 rectangle contains
the mathematical channel value.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import struct
from fractions import Fraction
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
PROBE_PATH = ROOT / "scripts/routea_repaired_owner_continuous_box_price_2670.py"
OUTPUT = ROOT / "results/2675_repaired_owner_cell_price_certificate.json"
CELLS = 8192
DEFAULT_CELL = CELLS // 2
RNDU = 2
CHANNEL_NAMES = ("base_M0", "base_D2", "correction_M0", "correction_D2")


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def binary64_record(value: float) -> dict:
    if not math.isfinite(value):
        raise ValueError("certificate endpoints must be finite binary64 values")
    bits = struct.unpack(">Q", struct.pack(">d", value))[0]
    exact = Fraction.from_float(value)
    return {
        "bits": f"0x{bits:016x}",
        "exact": str(exact),
    }


def upward_binary_operation(interval, op_name: str, left: float,
                            right: float) -> tuple[float, dict]:
    a, b, result = interval.M(), interval.M(), interval.M()
    try:
        a.set_d(left)
        b.set_d(right)
        operation = getattr(interval, op_name)
        operation(interval.BR(result.x), interval.BR(a.x),
                  interval.BR(b.x), RNDU)
        rounded = result.get_d(RNDU)
        return rounded, {
            "op": op_name.removeprefix("mpfr_") if op_name.startswith("mpfr_") else op_name,
            "left": binary64_record(left),
            "right": binary64_record(right),
            "result": binary64_record(rounded),
            "mpfr_result_rounded_up_to_binary64": True,
        }
    finally:
        a.clear()
        b.clear()
        result.clear()


def upward_unary_operation(interval, op_name: str,
                           argument: float) -> tuple[float, dict]:
    source, result = interval.M(), interval.M()
    try:
        source.set_d(argument)
        operation = getattr(interval, op_name)
        operation(interval.BR(result.x), interval.BR(source.x), RNDU)
        rounded = result.get_d(RNDU)
        return rounded, {
            "op": op_name.removeprefix("mpfr_") if op_name.startswith("mpfr_") else op_name,
            "argument": binary64_record(argument),
            "result": binary64_record(rounded),
            "mpfr_result_rounded_up_to_binary64": True,
        }
    finally:
        source.clear()
        result.clear()


def build_owner(probe, interval):
    repair = json.loads(probe.REPAIR.read_text(encoding="utf-8"))
    reread = json.loads(probe.REPAIR_REREAD.read_text(encoding="utf-8"))
    capture = json.loads(probe.CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    base, correction = probe.coefficient_arrays(repair["coefficient_rows"])
    coefficient_hashes = {
        "base": probe.md5_complex(base),
        "correction": probe.md5_complex(correction),
    }
    expected = {
        "base": reread["treatment"]["base_md5"],
        "correction": reread["treatment"]["corr_md5"],
    }
    captured = {
        "base": capture["base_md5"],
        "correction": capture["corr_md5"],
    }
    if coefficient_hashes != expected or coefficient_hashes == captured:
        raise AssertionError("loaded coefficients do not match the repaired owner")

    strip = load_module(
        "strip2675", ROOT / "scripts/routea_corrected_strip_envelope_2303.py")
    families, _base_capture, _correction_capture, _anchors = strip.load_owner()
    channels = probe.make_channels(interval, families, base, correction)
    for kernel, coefficients in zip(
            channels, (base, base, correction, correction)):
        probe.configure_exact_squared_radii(
            interval, kernel, families, coefficients)
    return coefficient_hashes, captured, families, channels


def price_cell(interval, channels, xlo: float, xhi: float,
               sigma: float) -> dict:
    width, width_step = upward_binary_operation(
        interval, "SUB", xhi, xlo)
    endpoint = xhi if sigma >= 0 else xlo
    exponent, exponent_step = upward_binary_operation(
        interval, "MUL", sigma, endpoint)
    weight, weight_step = upward_unary_operation(
        interval, "EXP", exponent)

    channel_rows = []
    total = 0.0
    total_steps = []
    for name, kernel in zip(CHANNEL_NAMES, channels):
        _no_zero, bounds, _floor = kernel.eval_box(xlo, xhi)
        rlo, rhi, ilo, ihi = bounds
        real_endpoint = max(abs(rlo), abs(rhi))
        imag_endpoint = max(abs(ilo), abs(ihi))
        real_square, real_square_step = upward_binary_operation(
            interval, "MUL", real_endpoint, real_endpoint)
        imag_square, imag_square_step = upward_binary_operation(
            interval, "MUL", imag_endpoint, imag_endpoint)
        norm_square, norm_square_step = upward_binary_operation(
            interval, "ADD", real_square, imag_square)
        norm, norm_step = upward_unary_operation(
            interval, "SQRT", norm_square)
        weighted_norm, weighted_norm_step = upward_binary_operation(
            interval, "MUL", width, norm)
        charge, charge_step = upward_binary_operation(
            interval, "MUL", weighted_norm, weight)
        row = {
            "name": name,
            "rectangle_endpoints": {
                "re_lo": binary64_record(rlo),
                "re_hi": binary64_record(rhi),
                "im_lo": binary64_record(ilo),
                "im_hi": binary64_record(ihi),
            },
            "corner_norm_chain": {
                "real_abs_max": binary64_record(real_endpoint),
                "imag_abs_max": binary64_record(imag_endpoint),
                "real_square": real_square_step,
                "imag_square": imag_square_step,
                "norm_square": norm_square_step,
                "norm_upper": norm_step,
            },
            "weighted_charge_chain": {
                "width_upper": width_step,
                "weight_upper": weight_step,
                "width_times_norm": weighted_norm_step,
                "charge_upper": charge_step,
            },
        }
        channel_rows.append(row)
        total, sum_step = upward_binary_operation(interval, "ADD", total, charge)
        total_steps.append(sum_step)

    original_256_total = interval.M()
    try:
        original_256_total.set_d(0.0)
        sigma_mp, endpoint_mp, exponent_mp, weight_mp = (
            interval.M(), interval.M(), interval.M(), interval.M())
        try:
            sigma_mp.set_d(sigma)
            endpoint_mp.set_d(endpoint)
            interval.MUL(interval.BR(exponent_mp.x), interval.BR(sigma_mp.x),
                         interval.BR(endpoint_mp.x), RNDU)
            interval.EXP(interval.BR(weight_mp.x), interval.BR(exponent_mp.x),
                          RNDU)
            width_mp = interval.M()
            width_mp.set_d(width)
            try:
                for kernel in channels:
                    _no_zero, bounds, _floor = kernel.eval_box(xlo, xhi)
                    rlo, rhi, ilo, ihi = bounds
                    rmax_mp, imax_mp = interval.M(), interval.M()
                    square_r, square_i = interval.M(), interval.M()
                    norm_sq, norm = interval.M(), interval.M()
                    term = interval.M()
                    try:
                        rmax_mp.set_d(max(abs(rlo), abs(rhi)))
                        imax_mp.set_d(max(abs(ilo), abs(ihi)))
                        interval.MUL(interval.BR(square_r.x), interval.BR(rmax_mp.x),
                                     interval.BR(rmax_mp.x), RNDU)
                        interval.MUL(interval.BR(square_i.x), interval.BR(imax_mp.x),
                                     interval.BR(imax_mp.x), RNDU)
                        interval.ADD(interval.BR(norm_sq.x), interval.BR(square_r.x),
                                     interval.BR(square_i.x), RNDU)
                        interval.SQRT(interval.BR(norm.x), interval.BR(norm_sq.x), RNDU)
                        interval.MUL(interval.BR(term.x), interval.BR(width_mp.x),
                                     interval.BR(norm.x), RNDU)
                        interval.MUL(interval.BR(term.x), interval.BR(term.x),
                                     interval.BR(weight_mp.x), RNDU)
                        interval.ADD(interval.BR(original_256_total.x),
                                     interval.BR(original_256_total.x),
                                     interval.BR(term.x), RNDU)
                    finally:
                        for value in (rmax_mp, imax_mp, square_r, square_i,
                                      norm_sq, norm, term):
                            value.clear()
            finally:
                width_mp.clear()
        finally:
            for value in (sigma_mp, endpoint_mp, exponent_mp, weight_mp):
                value.clear()
        reference = original_256_total.get_d(RNDU)
    finally:
        original_256_total.clear()

    if Fraction.from_float(total) < Fraction.from_float(reference):
        raise AssertionError("binary64-upward chain undercut the 256-bit control")
    budget = Fraction("74601530.30234718")
    if Fraction.from_float(total) > budget:
        raise AssertionError("single-cell upper charge exceeded the committed budget")

    return {
        "cell_endpoints": {
            "x_lo": binary64_record(xlo),
            "x_hi": binary64_record(xhi),
            "width_upper": width_step,
        },
        "sigma": binary64_record(sigma),
        "weight_endpoint": binary64_record(endpoint),
        "weight_chain": {
            "exponent_upper": exponent_step,
            "exp_upper": weight_step,
        },
        "channels": channel_rows,
        "cell_total_upper": binary64_record(total),
        "cell_accumulation": total_steps,
        "same_cell_256bit_reference_upper": binary64_record(reference),
        "upward_binary64_chain_dominates_256bit_control": True,
        "budget_exact": str(budget),
        "cell_charge_below_budget": True,
    }


def run(cell_index: int, cells: int, sigma: float) -> dict:
    if not 0 <= cell_index < cells:
        raise ValueError("cell index must lie in [0, cells)")
    probe = load_module("price2675", PROBE_PATH)
    interval = load_module(
        "interval2675", ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py")
    coefficient_hashes, captured, families, channels = build_owner(probe, interval)
    support = probe.audit_radius_rounding(families)["outward_support_radius"]
    grid = np.linspace(-support, support, cells + 1)
    xlo, xhi = float(grid[cell_index]), float(grid[cell_index + 1])
    cell = price_cell(interval, channels, xlo, xhi, sigma)
    return {
        "record": 2675,
        "status": "ONE_CELL_DIRECTED_BINARY64_PRICE_CERTIFICATE",
        "owner_coefficients_md5": coefficient_hashes,
        "captured_coefficients_md5": captured,
        "cell_index": cell_index,
        "partition_cells": cells,
        "support_radius_binary64": binary64_record(support),
        "mpfr_precision_bits": interval.PREC if hasattr(interval, "PREC") else 256,
        "source_sha256": {
            "exporter": sha256(Path(__file__)),
            "continuous_price_probe": sha256(PROBE_PATH),
            "interval_evaluator": sha256(
                ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"),
            "mpfr_binding": sha256(
                ROOT / "scripts/routea_weighted_zero_mpfr_exp_binding_2223.py"),
            "strip_owner": sha256(
                ROOT / "scripts/routea_corrected_strip_envelope_2303.py"),
            "repair_artifact": sha256(probe.REPAIR),
            "repair_reread_artifact": sha256(probe.REPAIR_REREAD),
            "owner_capture_artifact": sha256(probe.CAPTURE),
        },
        "cell": cell,
        "scope": (
            "the final 2242 rectangle endpoints and the one-cell scalar price; "
            "the theorem that each rectangle contains its mathematical channel "
            "value is not proved by this artifact"),
        "continuum_enclosure_proved": False,
        "actual_owner_identity_proved": False,
        "infinite_xi_tail_closed": False,
        "producer_go": False,
        "rh_claim": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cell", type=int, default=DEFAULT_CELL)
    parser.add_argument("--cells", type=int, default=CELLS)
    parser.add_argument("--sigma", type=float, default=-0.5)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    result = run(args.cell, args.cells, args.sigma)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "cell_index": result["cell_index"],
        "cell_endpoints": result["cell"]["cell_endpoints"],
        "channel_bounds": [
            row["rectangle_endpoints"] for row in result["cell"]["channels"]],
        "cell_total_upper": result["cell"]["cell_total_upper"],
        "same_cell_256bit_reference_upper":
            result["cell"]["same_cell_256bit_reference_upper"],
        "upward_binary64_chain_dominates_256bit_control":
            result["cell"]["upward_binary64_chain_dominates_256bit_control"],
        "scope": result["scope"],
    }, indent=2))


if __name__ == "__main__":
    main()
