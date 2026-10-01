"""Independent high-precision containment control for the 2242 point boxes.

The interval evaluator remains the object under test.  The reference uses
the stored binary64 operands converted to exact rationals and evaluates the
same finite family formula with mpmath at high precision.  This is a sampled
control, not a proof for every real point or a Lean numeric import.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import argparse
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parents[1]


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def exact_float(value: float) -> mp.mpf:
    fraction = Fraction.from_float(float(value))
    return mp.mpf(fraction.numerator) / fraction.denominator


def reference_value(families, coefficients, order: int, x: float) -> mp.mpc:
    xx = exact_float(x)
    total = mp.mpc(0)
    for (a_raw, theta_raw), coefficient in zip(families, coefficients):
        a = exact_float(a_raw)
        theta = exact_float(theta_raw)
        u = xx / a
        q = 1 - u * u
        if q <= 0:
            continue
        phi = mp.exp(-30 / q)
        e1 = -(60 / a) * u / (q * q)
        if order == 0:
            factor = 1
        else:
            e2 = -(60 / (a * a)) * (1 / (q * q) + 4 * u * u / (q ** 3))
            factor = e2 + (e1 + 1j * theta) ** 2
        total += (exact_float(complex(coefficient).real) +
                  1j * exact_float(complex(coefficient).imag)) * phi \
                 * mp.exp(1j * theta * xx) * factor
    return total


def main(allow_evaluator_revision: bool = False,
         output_name: str = "2397_pointbox_mpmath_containment_control.json") -> dict:
    worker_path = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator_path = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    artifact = json.loads(
        (ROOT / "results/2385_shared_geometry_776611.json").read_text())
    require(artifact["source_sha256"] == sha256(worker_path),
            "2359 source hash mismatch")
    evaluator_hash_matches = artifact["evaluator_source_sha256"] == sha256(evaluator_path)
    if not allow_evaluator_revision:
        require(evaluator_hash_matches, "2242 evaluator source hash mismatch")

    evaluator = load("containment_control_2397", evaluator_path)
    strip = load("strip_containment_control_2397",
                  ROOT / "scripts/routea_corrected_strip_envelope_2303.py")
    families, base, correction, _ = strip.load_owner()
    families = strip.corrected_fam(families)
    kernels = [
        (evaluator.Kernel(families, base, 0), base, 0),
        (evaluator.Kernel(families, base, 2), base, 2),
        (evaluator.Kernel(families, correction, 0), correction, 0),
        (evaluator.Kernel(families, correction, 2), correction, 2),
    ]
    radius = max(float(a) * float(a) for a, _theta in families)
    nodes = 1001
    grid = np.linspace(-radius, radius, nodes)
    worst = 0.0
    checked = 0
    worst_row = None
    failures = []
    with mp.workdps(90):
        for index, point in enumerate(grid):
            geometry_cache = [None] * len(kernels[0][0].recs)
            for channel, (kernel, coefficients, order) in enumerate(kernels):
                if channel == 0:
                    geometry_cache = [None] * len(kernel.recs)
                _ok, bounds, _floor = kernel.eval_box(
                    float(point), float(point), geometry_cache)
                value = reference_value(families, coefficients, order,
                                        float(point))
                re, im = mp.re(value), mp.im(value)
                rlo, rhi, ilo, ihi = map(mp.mpf, bounds)
                violation = max(mp.mpf(0), rlo - re, re - rhi,
                                ilo - im, im - ihi)
                scale = max(mp.mpf(1), abs(re), abs(im),
                            abs(rlo), abs(rhi), abs(ilo), abs(ihi))
                relative = float(violation / scale)
                checked += 1
                if relative > worst:
                    worst = relative
                    worst_row = [index, float(point), channel, str(violation)]
                if violation > 0:
                    float_value = evaluator.channel_arrays(
                        families, coefficients, order, np.asarray([float(point)]))[0][0]
                    failures.append([index, float(point), channel,
                                     str(violation), str(re), str(im),
                                     [str(rlo), str(rhi), str(ilo), str(ihi)],
                                     [float(float_value.real), float(float_value.imag)]])
    status_prefix = ("POINTBOX_MPMATH_CONTAINMENT_REPAIRED_PROBE"
                     if allow_evaluator_revision else
                     "POINTBOX_MPMATH_CONTAINMENT_CONTROL")
    status = (status_prefix + "_PASS"
              if not failures else status_prefix + "_FAIL")
    result = {
        "record": 2398 if allow_evaluator_revision else 2397,
        "status": status,
        "source_hashes_match": evaluator_hash_matches,
        "evaluator_revision_probe": allow_evaluator_revision,
        "artifact_evaluator_source_sha256": artifact["evaluator_source_sha256"],
        "current_evaluator_source_sha256": sha256(evaluator_path),
        "nodes": nodes,
        "channels": 4,
        "checked_point_channel_values": checked,
        "mpmath_dps": 90,
        "stored_operands_converted_exactly": True,
        "containment_failures": len(failures),
        "first_failure": failures[0] if failures else None,
        "worst_relative_violation": worst,
        "worst_row": worst_row,
        "lean_numeric_imported": False,
        "full_real_domain_enclosure_proved": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results" / output_name
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-evaluator-revision", action="store_true")
    parser.add_argument("--output", default="2397_pointbox_mpmath_containment_control.json")
    args = parser.parse_args()
    main(args.allow_evaluator_revision, args.output)
