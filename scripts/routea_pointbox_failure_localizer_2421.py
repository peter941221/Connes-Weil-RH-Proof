"""Localize a sampled point-box escape without changing the evaluator."""

from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def exact(value: float) -> mp.mpf:
    value = float(value)
    return mp.mpf(value.as_integer_ratio()[0]) / value.as_integer_ratio()[1]


def reference(families, coefficients, order: int, x: float) -> mp.mpc:
    xx = exact(x)
    total = mp.mpc(0)
    for (a0, theta0), coefficient in zip(families, coefficients):
        a, theta = exact(a0), exact(theta0)
        u = xx / a
        q = 1 - u * u
        if q <= 0:
            continue
        phi = mp.exp(-30 / q)
        e1 = -(60 / a) * u / q ** 2
        factor = 1
        if order == 2:
            e2 = -(60 / a ** 2) * (1 / q ** 2 + 4 * u ** 2 / q ** 3)
            factor = e2 + (e1 + 1j * theta) ** 2
        c = exact(float(np.real(coefficient))) + 1j * exact(float(np.imag(coefficient)))
        total += c * phi * mp.exp(1j * theta * xx) * factor
    return total


def main() -> None:
    evaluator = load("localizer_eval", ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py")
    strip = load("localizer_strip", ROOT / "scripts/routea_corrected_strip_envelope_2303.py")
    families, base, correction, _ = strip.load_owner()
    families = strip.corrected_fam(families)
    x = -4.767413698560006
    rows = []
    with mp.workdps(100):
        for label, coefficients, order in (
            ("base_M0", base, 0), ("base_D2", base, 2),
            ("corr_M0", correction, 0), ("corr_D2", correction, 2)):
            kernel = evaluator.Kernel(families, coefficients, order)
            fresh = kernel.eval_box(x, x, None)[1]
            cache = [None] * len(kernel.recs)
            cached_first = kernel.eval_box(x, x, cache)[1]
            cached_second = kernel.eval_box(x, x, cache)[1]
            value = reference(families, coefficients, order, x)
            rows.append({
                "channel": label,
                "reference": [str(mp.re(value)), str(mp.im(value))],
                "fresh": [str(v) for v in fresh],
                "cached_first": [str(v) for v in cached_first],
                "cached_second": [str(v) for v in cached_second],
                "fresh_contains": fresh[0] <= float(mp.re(value)) <= fresh[1]
                and fresh[2] <= float(mp.im(value)) <= fresh[3],
                "cached_contains": cached_second[0] <= float(mp.re(value)) <= cached_second[1]
                and cached_second[2] <= float(mp.im(value)) <= cached_second[3],
            })
    print(rows)


if __name__ == "__main__":
    main()
