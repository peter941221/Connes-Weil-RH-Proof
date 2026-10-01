"""2358: directed point-box smoke for the 2303 nodal-upper bridge.

This is deliberately a smoke probe, not a certificate.  It evaluates the
four corrected-owner channels with the directed MPFR interval evaluator from
2242 on zero-width boxes, then integrates pointwise upper magnitudes on a
configurable coarse grid at the binding sigma.  The decision is whether the
natural interval evaluator explodes before the full 240001-node bridge is
attempted.
"""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {filename}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def interval_abs_upper(bounds):
    rlo, rhi, ilo, ihi = bounds
    return math.hypot(max(abs(rlo), abs(rhi)), max(abs(ilo), abs(ihi)))


def run(nodes=1001, sigma=-0.5):
    if nodes < 3 or nodes % 2 == 0:
        raise ValueError("nodes must be odd and at least three")
    strip = load("strip2358", "routea_corrected_strip_envelope_2303.py")
    interval = load("interval2358", "routea_weighted_zero_zero_count_certificate_2242.py")
    families, base, correction, _ = strip.load_owner()
    corrected = strip.corrected_fam(families)
    radius = max(a for a, _ in corrected)
    grid = np.linspace(-radius, radius, nodes)
    kernels = [
        interval.Kernel(corrected, base, 0),
        interval.Kernel(corrected, base, 2),
        interval.Kernel(corrected, correction, 0),
        interval.Kernel(corrected, correction, 2),
    ]
    integrands = np.zeros((4, nodes), dtype=float)
    for index, point in enumerate(grid):
        weight = math.exp(sigma * float(point))
        for channel, kernel in enumerate(kernels):
            _nonzero, bounds, _floor = kernel.eval_box(float(point), float(point))
            integrands[channel, index] = interval_abs_upper(bounds) * weight
    integrals = [float(np.trapezoid(values, grid)) for values in integrands]
    minimum = min(integrals[1] * integrals[2], integrals[3] * integrals[0])
    baseline = json.loads(
        (ROOT / "results/2303_corrected_strip_envelope.json").read_text()
    )
    row = next(row for row in baseline["grid_rows"] if row["j"] == round(100 * sigma))
    return {
        "record": 2358,
        "status": "DIRECTED_NODE_INTERVAL_SMOKE_NOT_CERTIFICATE",
        "nodes": nodes,
        "sigma": sigma,
        "radius": radius,
        "interval_integrals": integrals,
        "interval_min_product": minimum,
        "stored_point": row["point"],
        "stored_B_point": row["B_point"],
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "evaluator_source_sha256": hashlib.sha256(
            (ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py").read_bytes()
        ).hexdigest(),
        "full_grid_nodal_upper_proved": False,
        "coordinate_identity_proved": False,
        "lean_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=1001)
    parser.add_argument("--sigma", type=float, default=-0.5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.nodes, args.sigma)
    output = args.output or ROOT / "results/2358_nodal_interval_smoke.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in
                      ("status", "nodes", "sigma", "interval_integrals",
                       "interval_min_product")}, indent=2))
