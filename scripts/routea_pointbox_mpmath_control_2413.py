"""Finer independent containment control for the repaired 2411 evaluator.

This is a sampled control at a parameterized 5001-point grid.  It uses exact
rational conversions of stored binary64 operands and 90-digit mpmath values;
it is not a full-domain proof or a Lean numeric import.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2411_repaired_shared_geometry_776611.json"
EVALUATOR = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
WORKER = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
STRIP = ROOT / "scripts/routea_corrected_strip_envelope_2303.py"


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
    return mp.mpf(numerator) / denominator


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


def main(nodes: int = 5001, allow_evaluator_revision: bool = False) -> dict:
    artifact = json.loads(ARTIFACT.read_text())
    evaluator_hash_matches = artifact["evaluator_source_sha256"] == sha256(EVALUATOR)
    require = lambda condition, message: (_ for _ in ()).throw(
        AssertionError(message)) if not condition else None
    require(artifact["source_sha256"] == sha256(WORKER), "worker hash mismatch")
    require(evaluator_hash_matches or allow_evaluator_revision,
            "evaluator hash mismatch")

    evaluator = load("containment_2413", EVALUATOR)
    strip = load("strip_2413", STRIP)
    families, base, correction, _ = strip.load_owner()
    families = strip.corrected_fam(families)
    kernels = [
        (evaluator.Kernel(families, base, 0), base, 0),
        (evaluator.Kernel(families, base, 2), base, 2),
        (evaluator.Kernel(families, correction, 0), correction, 0),
        (evaluator.Kernel(families, correction, 2), correction, 2),
    ]
    radius = max(float(a) * float(a) for a, _theta in families)
    grid = np.linspace(-radius, radius, nodes)
    failures = []
    worst = mp.mpf(0)
    worst_row = None
    checked = 0
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
                scale = max(mp.mpf(1), abs(re), abs(im), abs(rlo),
                            abs(rhi), abs(ilo), abs(ihi))
                relative = violation / scale
                checked += 1
                if relative > worst:
                    worst = relative
                    worst_row = [index, float(point), channel, str(violation)]
                if violation > 0:
                    failures.append({
                        "index": index,
                        "point": float(point),
                        "channel": channel,
                        "violation": str(violation),
                        "reference_re": str(re),
                        "reference_im": str(im),
                        "bounds": [str(rlo), str(rhi), str(ilo), str(ihi)],
                    })

    result = {
        "record": 2413,
        "status": "POINTBOX_MPMATH_5001_CONTROL_PASS" if not failures
                  else "POINTBOX_MPMATH_5001_CONTROL_FAIL",
        "artifact": str(ARTIFACT.relative_to(ROOT)),
        "source_hashes_match": evaluator_hash_matches,
        "evaluator_revision_probe": allow_evaluator_revision,
        "nodes": nodes,
        "channels": 4,
        "checked_point_channel_values": checked,
        "mpmath_dps": 90,
        "stored_operands_converted_exactly": True,
        "public_hull_ulp_margin": 4,
        "containment_failures": len(failures),
        "first_failure": failures[0] if failures else None,
        "worst_relative_violation": float(worst),
        "worst_row": worst_row,
        "full_real_domain_enclosure_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2413_pointbox_mpmath_control.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-evaluator-revision", action="store_true")
    parser.add_argument("--nodes", type=int, default=5001)
    args = parser.parse_args()
    main(args.nodes, args.allow_evaluator_revision)
