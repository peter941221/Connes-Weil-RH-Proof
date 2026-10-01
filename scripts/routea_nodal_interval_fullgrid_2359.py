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
from fractions import Fraction
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
_WORKER = None
_WORKER_GRID = None
_WORKER_DIRECTED_ACC = None
_WORKER_DIRECTED_TERM = None
_WORKER_INTERVAL = None


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
    global _WORKER, _WORKER_GRID, _WORKER_DIRECTED_ACC, _WORKER_DIRECTED_TERM, _WORKER_INTERVAL
    start, stop, nodes, sigma, radius = task
    if _WORKER is None:
        strip = load("strip2359", "routea_corrected_strip_envelope_2303.py")
        interval = load("interval2359", "routea_weighted_zero_zero_count_certificate_2242.py")
        _WORKER_INTERVAL = interval
        families, base, correction, _ = strip.load_owner()
        corrected = strip.corrected_fam(families)
        _WORKER = (
            interval.Kernel(corrected, base, 0),
            interval.Kernel(corrected, base, 2),
            interval.Kernel(corrected, correction, 0),
            interval.Kernel(corrected, correction, 2),
        )
        _WORKER_GRID = np.linspace(-radius, radius, nodes)
        _WORKER_DIRECTED_ACC = [interval.M() for _ in range(4)]
        for accumulator in _WORKER_DIRECTED_ACC:
            accumulator.set_d(0.0)
        _WORKER_DIRECTED_TERM = interval.M()
    else:
        # A fork worker services multiple spans; every span must have its own
        # directed accumulator or the parent would double-count prior spans.
        for accumulator in _WORKER_DIRECTED_ACC:
            accumulator.set_d(0.0)
    sums = np.zeros(4, dtype=float)
    exact_sums = [Fraction(0) for _ in range(4)]
    for index in range(start, stop):
        point = float(_WORKER_GRID[index])
        factor = math.exp(sigma * point)
        cell_weight = 0.5 if index == 0 or index == nodes - 1 else 1.0
        for channel, kernel in enumerate(_WORKER):
            _ok, bounds, _floor = kernel.eval_box(point, point)
            term = cell_weight * interval_abs_upper(bounds) * factor
            sums[channel] += term
            exact_sums[channel] += Fraction.from_float(term)
            _WORKER_DIRECTED_TERM.set_d(term)
            _WORKER_INTERVAL.ADD(
                _WORKER_INTERVAL.BR(_WORKER_DIRECTED_ACC[channel].x),
                _WORKER_INTERVAL.BR(_WORKER_DIRECTED_ACC[channel].x),
                _WORKER_INTERVAL.BR(_WORKER_DIRECTED_TERM.x),
                _WORKER_INTERVAL.RNDU,
            )
    return (start, sums.tolist(), [str(value) for value in exact_sums],
            [accumulator.get_d(_WORKER_INTERVAL.RNDU) for accumulator in _WORKER_DIRECTED_ACC])


def run(nodes=240001, sigma=-0.5, workers=1, span=20001):
    if nodes < 3 or nodes % 2 == 0:
        raise ValueError("nodes must be odd and at least three")
    if workers < 1 or span < 1:
        raise ValueError("workers and span must be positive")
    strip = load("strip2359main", "routea_corrected_strip_envelope_2303.py")
    families, _base, _correction, _ = strip.load_owner()
    radius = max(a * a for a, _ in families)
    grid = np.linspace(-radius, radius, nodes)
    coordinate_gaps = [
        abs(Fraction(float(point)) -
            (Fraction(-radius) + Fraction(2.0 * radius) * index / (nodes - 1)))
        for index, point in enumerate(grid)
    ]
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
    exact_total = [sum((Fraction(part[2][channel]) for part in parts), Fraction(0))
                   for channel in range(4)]
    dx = 2.0 * radius / (nodes - 1)
    integrals = (dx * total).tolist()
    exact_dx = Fraction.from_float(dx)
    exact_integrals = [exact_dx * value for value in exact_total]
    accumulation_float_gap = [
        abs(Fraction.from_float(float(value)) - exact_integrals[channel])
        for channel, value in enumerate(integrals)
    ]
    interval_main = load("interval2359main_acc", "routea_weighted_zero_zero_count_certificate_2242.py")
    directed_total = [interval_main.M() for _ in range(4)]
    directed_span = interval_main.M()
    directed_dx = interval_main.M()
    directed_integral = interval_main.M()
    for accumulator in directed_total:
        accumulator.set_d(0.0)
    for part in parts:
        for channel in range(4):
            directed_span.set_d(part[3][channel])
            interval_main.ADD(
                interval_main.BR(directed_total[channel].x),
                interval_main.BR(directed_total[channel].x),
                interval_main.BR(directed_span.x),
                interval_main.RNDU,
            )
    directed_dx.set_d(dx)
    directed_integrals = []
    for accumulator in directed_total:
        interval_main.MUL(
            interval_main.BR(directed_integral.x),
            interval_main.BR(accumulator.x),
            interval_main.BR(directed_dx.x),
            interval_main.RNDU,
        )
        directed_integrals.append(directed_integral.get_d(interval_main.RNDU))
    minimum = min(integrals[1] * integrals[2], integrals[3] * integrals[0])
    return {
        "record": 2359,
        "status": "DIRECTED_NODE_INTERVAL_FULL_GRID_SMOKE_NOT_CERTIFICATE",
        "nodes": nodes,
        "sigma": sigma,
        "workers": workers,
        "span": span,
        "radius": radius,
        "coordinate_difference_count": sum(gap != 0 for gap in coordinate_gaps),
        "coordinate_max_fraction_gap": str(max(coordinate_gaps)),
        "interval_integrals": integrals,
        "exact_binary64_term_integrals": [str(value) for value in exact_integrals],
        "accumulation_float_gap": [str(value) for value in accumulation_float_gap],
        "accumulation_float_gap_max": str(max(accumulation_float_gap)),
        "accumulation_is_exact_term_sum": True,
        "accumulation_is_directed_mpfr": False,
        "directed_mpfr_term_accumulation_integrals": directed_integrals,
        "directed_mpfr_term_accumulation": True,
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
