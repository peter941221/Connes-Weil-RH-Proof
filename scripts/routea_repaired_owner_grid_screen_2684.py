"""Screen the complete repaired-owner 8192-cell partition.

This is a numerical design screen, not a proof.  It reuses the audited 2242
natural interval evaluator and the 2675 directed binary64 price convention,
but keeps the owner/evaluator initialized once for the whole grid.  The
artifact is deliberately compact: endpoint bit patterns are retained so the
screen can be replayed without decimal-parser ambiguity.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import multiprocessing as mp
import struct
from fractions import Fraction
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
PROBE_PATH = ROOT / "scripts/routea_repaired_owner_continuous_box_price_2670.py"
PRICE_PATH = ROOT / "scripts/routea_repaired_owner_cell_price_certificate_2675.py"
INTERVAL_PATH = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
STRIP_PATH = ROOT / "scripts/routea_corrected_strip_envelope_2303.py"
OUTPUT = ROOT / "results/2684_repaired_owner_8192_cell_grid_screen.json"

CELLS = 8192
SIGMA = -0.5
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


def bits(value: float) -> str:
    raw = struct.unpack(">Q", struct.pack(">d", value))[0]
    return f"0x{raw:016x}"


def exact(value: float) -> str:
    return str(Fraction.from_float(value))


def record(value: float) -> dict:
    return {"bits": bits(value), "exact": exact(value)}


def upward_binary_operation(interval, op_name: str, left: float,
                            right: float) -> float:
    a, b, result = interval.M(), interval.M(), interval.M()
    try:
        a.set_d(left)
        b.set_d(right)
        getattr(interval, op_name)(interval.BR(result.x), interval.BR(a.x),
                                   interval.BR(b.x), RNDU)
        return result.get_d(RNDU)
    finally:
        a.clear()
        b.clear()
        result.clear()


def upward_unary_operation(interval, op_name: str, value: float) -> float:
    source, result = interval.M(), interval.M()
    try:
        source.set_d(value)
        getattr(interval, op_name)(interval.BR(result.x), interval.BR(source.x), RNDU)
        return result.get_d(RNDU)
    finally:
        source.clear()
        result.clear()


def load_owner(probe, interval):
    repair = json.loads(probe.REPAIR.read_text(encoding="utf-8"))
    reread = json.loads(probe.REPAIR_REREAD.read_text(encoding="utf-8"))
    capture = json.loads(probe.CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    base, correction = probe.coefficient_arrays(repair["coefficient_rows"])
    hashes = {"base": probe.md5_complex(base), "correction": probe.md5_complex(correction)}
    expected = {"base": reread["treatment"]["base_md5"],
                "correction": reread["treatment"]["corr_md5"]}
    captured = {"base": capture["base_md5"], "correction": capture["corr_md5"]}
    if hashes != expected or hashes == captured:
        raise AssertionError("loaded coefficients do not match repaired treatment")

    strip = load_module("strip2684", STRIP_PATH)
    families, _base_capture, _correction_capture, anchors = strip.load_owner()
    channels = probe.make_channels(interval, families, base, correction)
    for kernel, coefficients in zip(channels, (base, base, correction, correction)):
        probe.configure_exact_squared_radii(interval, kernel, families, coefficients)
    return hashes, captured, families, channels, anchors


def screen_cell(interval, channels, xlo: float, xhi: float, sigma: float) -> list:
    width = upward_binary_operation(interval, "SUB", xhi, xlo)
    endpoint = xhi if sigma >= 0.0 else xlo
    exponent = upward_binary_operation(interval, "MUL", sigma, endpoint)
    weight = upward_unary_operation(interval, "EXP", exponent)

    rows = []
    total = 0.0
    for name, kernel in zip(CHANNEL_NAMES, channels):
        _no_zero, bounds, _floor = kernel.eval_box(xlo, xhi)
        rlo, rhi, ilo, ihi = bounds
        rmax = max(abs(rlo), abs(rhi))
        imax = max(abs(ilo), abs(ihi))
        real_square = upward_binary_operation(interval, "MUL", rmax, rmax)
        imag_square = upward_binary_operation(interval, "MUL", imax, imax)
        norm_square = upward_binary_operation(interval, "ADD", real_square, imag_square)
        norm = upward_unary_operation(interval, "SQRT", norm_square)
        term = upward_binary_operation(interval, "MUL", width, norm)
        charge = upward_binary_operation(interval, "MUL", term, weight)
        total = upward_binary_operation(interval, "ADD", total, charge)
        rows.append([bits(rlo), bits(rhi), bits(ilo), bits(ihi),
                     bits(norm), bits(charge)])
    # Fixed positions keep the artifact small while preserving every exact
    # binary64 value. Channel order is recorded once in the top-level header.
    return [bits(xlo), bits(xhi), bits(width), bits(weight), rows, bits(total)]


def screen_range(args: tuple[int, int, int, float]) -> list[list]:
    """Initialize one evaluator per process and screen a contiguous range."""
    cells, start, stop, sigma = args
    probe = load_module(f"probe2684_worker_{start}", PROBE_PATH)
    interval = load_module(f"interval2684_worker_{start}", INTERVAL_PATH)
    _hashes, _captured, families, channels, _anchors = load_owner(probe, interval)
    support = probe.audit_radius_rounding(families)["outward_support_radius"]
    grid = np.linspace(-support, support, cells + 1)
    result = []
    for index in range(start, stop):
        cell = screen_cell(interval, channels, float(grid[index]),
                           float(grid[index + 1]), sigma)
        cell.insert(0, index)
        result.append(cell)
    return result


def float_from_bits(value: str) -> float:
    return struct.unpack(">d", struct.pack(">Q", int(value, 16)))[0]


def verify_grid(cells: list[list], expected_count: int) -> dict:
    if len(cells) != expected_count:
        raise AssertionError("cell count does not match the requested partition")
    for index, cell in enumerate(cells):
        if cell[0] != index:
            raise AssertionError(f"cell index/order mismatch at {index}")
        if index and cells[index - 1][2] != cell[1]:
            raise AssertionError(f"adjacent endpoint mismatch at cell {index}")
    if expected_count != CELLS:
        return {"adjacent_endpoint_pairs": expected_count - 1,
                "record2675_cell_replay": "NOT_APPLICABLE"}

    reference = json.loads(
        (ROOT / "results/2675_repaired_owner_cell_price_certificate.json")
        .read_text(encoding="utf-8"))
    middle = cells[CELLS // 2]
    ref_cell = reference["cell"]
    if middle[1] != ref_cell["cell_endpoints"]["x_lo"]["bits"] \
            or middle[2] != ref_cell["cell_endpoints"]["x_hi"]["bits"]:
        raise AssertionError("middle-cell endpoints do not match record 2675")
    for channel, row in zip(CHANNEL_NAMES, middle[5]):
        ref_row = next(item for item in ref_cell["channels"]
                       if item["name"] == channel)
        for coord, key in enumerate(("re_lo", "re_hi", "im_lo", "im_hi")):
            if row[coord] != ref_row["rectangle_endpoints"][key]["bits"]:
                raise AssertionError(f"{channel} {key} differs from record 2675")
        if row[5] != ref_row["weighted_charge_chain"]["charge_upper"]["result"]["bits"]:
            raise AssertionError(f"{channel} charge differs from record 2675")
    if middle[6] != ref_cell["cell_total_upper"]["bits"]:
        raise AssertionError("middle-cell total differs from record 2675")
    return {"adjacent_endpoint_pairs": expected_count - 1,
            "record2675_cell_replay": "BITWISE_PASS"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=CELLS)
    parser.add_argument("--sigma", type=float, default=SIGMA)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    if args.cells < 1:
        raise ValueError("cells must be positive")

    probe = load_module("probe2684", PROBE_PATH)
    interval = load_module("interval2684", INTERVAL_PATH)
    hashes, captured, families, channels, anchors = load_owner(probe, interval)
    support = probe.audit_radius_rounding(families)["outward_support_radius"]
    grid = np.linspace(-support, support, args.cells + 1)

    if args.workers < 1:
        raise ValueError("workers must be positive")
    ranges = []
    for worker in range(min(args.workers, args.cells)):
        start = (args.cells * worker) // min(args.workers, args.cells)
        stop = (args.cells * (worker + 1)) // min(args.workers, args.cells)
        ranges.append((args.cells, start, stop, args.sigma))
    if args.workers == 1:
        cells = screen_range(ranges[0])
    else:
        context = mp.get_context("fork")
        with context.Pool(processes=min(args.workers, args.cells)) as pool:
            chunks = pool.map(screen_range, ranges)
        cells = [cell for chunk in chunks for cell in chunk]
        cells.sort(key=lambda row: row[0])
    total = Fraction(0)
    worst = None
    for cell in cells:
        cell_total = float_from_bits(cell[6])
        total += Fraction.from_float(cell_total)
        if worst is None or cell_total > worst["total"]:
            worst = {"cell_index": cell[0], "total": cell_total}

    budget = Fraction("74601530.30234718")
    integrity = verify_grid(cells, args.cells)
    result = {
        "record": 2684,
        "status": ("REPAIRED_OWNER_GRID_SCREEN_BUDGET_PASS" if total <= budget
                   else "REPAIRED_OWNER_GRID_SCREEN_OVER_BUDGET"),
        "scope": (
            "all partition cells evaluated with the 2242 natural interval "
            "evaluator and 2675 directed binary64 arithmetic; this is a "
            "numerical screen, not a continuum Lean enclosure"),
        "cells": args.cells,
        "channel_order": list(CHANNEL_NAMES),
        "cell_encoding": (
            "[index, x_lo_bits, x_hi_bits, width_upper_bits, weight_upper_bits, "
            "[[re_lo, re_hi, im_lo, im_hi, norm_upper, charge_upper]_bits per channel], "
            "total_upper_bits]; all bits are IEEE-754 binary64"),
        "sigma": record(args.sigma),
        "support_radius": record(support),
        "owner_coefficients_md5": hashes,
        "captured_coefficients_md5": captured,
        "owner_anchors": anchors,
        "integrity_checks": integrity,
        "source_sha256": {
            "grid_screen": sha256(Path(__file__)),
            "continuous_price_probe": sha256(PROBE_PATH),
            "cell_exporter": sha256(PRICE_PATH),
            "interval_evaluator": sha256(INTERVAL_PATH),
            "strip_owner": sha256(STRIP_PATH),
        },
        "total_upper_sum": record(float(total)),
        "budget": str(budget),
        "budget_ratio": float(total / budget),
        "below_knownError2109": total <= budget,
        "worst_cell": worst,
        "cells_data": cells,
        "continuum_enclosure_proved": False,
        "lean_numeric_imported": False,
        "actual_owner_identity_proved": False,
        "infinite_xi_tail_closed": False,
        "producer_go": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, sort_keys=True,
                                       separators=(",", ":")) + "\n",
                           encoding="utf-8")
    print(json.dumps({
        "record": result["record"], "status": result["status"],
        "cells": result["cells"], "total_upper_sum": result["total_upper_sum"],
        "budget_ratio": result["budget_ratio"], "below_knownError2109": result["below_knownError2109"],
        "worst_cell": result["worst_cell"],
    }, indent=2))


if __name__ == "__main__":
    main()
