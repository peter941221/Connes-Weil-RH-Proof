"""2359: full-grid directed point-box replay for the nodal-upper target.

The evaluator is the certified directed MPFR point-box evaluator from 2242.
This run covers the producer's 240001-point x order at one binding sigma. It
is still a diagnostic: the directed accumulator and composite-trapezoid
remainder have not yet been imported as a theorem.
"""
import argparse
import hashlib
import importlib.util
import json
import math
import multiprocessing as mp
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
_WORKER = None


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


def worker_span(task):
    global _WORKER
    if _WORKER is None:
        strip = load("strip2359", "routea_corrected_strip_envelope_2303.py")
        interval = load("interval2359", "routea_weighted_zero_zero_count_certificate_2242.py")
        families, base, correction, _ = strip.load_owner()
        corrected = strip.corrected_fam(families)
        _WORKER = (
            interval.Kernel(corrected, base, 0),
            interval.Kernel(corrected, base, 2),
            interval.Kernel(corrected, correction, 0),
            interval.Kernel(corrected, correction, 2),
        )
    start, stop, nodes, sigma, radius = task
    sums = np.zeros(4, dtype=float)
    for index in range(start, stop):
        point = -radius + (2.0 * radius) * index / (nodes - 1)
        factor = math.exp(sigma * point)
        cell_weight = 0.5 if index == 0 or index == nodes - 1 else 1.0
        for channel, kernel in enumerate(_WORKER):
            _ok, bounds, _floor = kernel.eval_box(point, point)
            sums[channel] += cell_weight * interval_abs_upper(bounds) * factor
    return start, sums.tolist()


def run(nodes=240001, sigma=-0.5, workers=1, span=20001):
    if nodes < 3 or nodes % 2 == 0:
        raise ValueError("nodes must be odd and at least three")
    if workers < 1 or span < 1:
        raise ValueError("workers and span must be positive")
    strip = load("strip2359main", "routea_corrected_strip_envelope_2303.py")
    families, _base, _correction, _ = strip.load_owner()
    radius = max(a * a for a, _ in families)
    tasks = [(start, min(start + span, nodes), nodes, sigma, radius)
             for start in range(0, nodes, span)]
    if workers == 1:
        parts = [worker_span(task) for task in tasks]
    else:
        context = mp.get_context("fork")
        with context.Pool(processes=workers) as pool:
            parts = list(pool.imap(worker_span, tasks, chunksize=1))
    parts.sort(key=lambda item: item[0])
    total = np.sum(np.asarray([part[1] for part in parts], dtype=float), axis=0)
    dx = 2.0 * radius / (nodes - 1)
    integrals = (dx * total).tolist()
    minimum = min(integrals[1] * integrals[2], integrals[3] * integrals[0])
    return {
        "record": 2359,
        "status": "DIRECTED_NODE_INTERVAL_FULL_GRID_SMOKE_NOT_CERTIFICATE",
        "nodes": nodes,
        "sigma": sigma,
        "workers": workers,
        "span": span,
        "radius": radius,
        "interval_integrals": integrals,
        "interval_min_product": minimum,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "evaluator_source_sha256": hashlib.sha256(
            (ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py").read_bytes()
        ).hexdigest(),
        "directed_accumulation_theorem_proved": False,
        "trapezoid_remainder_proved": False,
        "coordinate_identity_proved": False,
        "lean_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=240001)
    parser.add_argument("--sigma", type=float, default=-0.5)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--span", type=int, default=20001)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.nodes, args.sigma, args.workers, args.span)
    output = args.output or ROOT / "results/2359_nodal_interval_fullgrid.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in
                      ("status", "nodes", "workers", "span",
                       "interval_integrals", "interval_min_product")}, indent=2))
