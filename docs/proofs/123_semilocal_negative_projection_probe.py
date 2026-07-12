#!/usr/bin/env python3
"""Screen the source-shaped one-sided semilocal prolate trace.

This probe uses the exact Meixner--Lambert Jacobi sections from proof 033.
For a Schwartz multiplier exp(-tau D^2), it measures

    Tr(exp(-tau D^2) P_- exp(-tau D^2)),

where P_- is the negative spectral projection of the finite prolate section.
The experiment is only a convergence/death screen. Finite Jacobi sections do
not prove the infinite self-adjoint realization or a Weil trace identity.
"""

import importlib.util
from pathlib import Path

import numpy as np


def load_guarded_probe():
    path = Path(__file__).with_name("033_guarded_prolate_cross_energy_probe.py")
    specification = importlib.util.spec_from_file_location("guarded_probe", path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


GUARDED = load_guarded_probe()


def prolate_operator(jacobi: np.ndarray, cutoff: float) -> np.ndarray:
    size = jacobi.shape[0]
    grading = np.diag(np.arange(size, dtype=float))
    return (
        -(jacobi @ jacobi)
        + 2 * np.pi * cutoff**2 * (4 * grading + np.eye(size))
        - 0.25 * np.eye(size)
    )


def one_sided_smoothed_trace(
    jacobi: np.ndarray,
    cutoff: float,
    tau: float,
    tail_fraction: float = 0.25,
):
    values, vectors = np.linalg.eigh(prolate_operator(jacobi, cutoff))
    negative_indices = np.flatnonzero(values < 0)
    tail_start = int((1 - tail_fraction) * jacobi.shape[0])
    accepted = list(negative_indices)
    rejected = []
    for index in negative_indices:
        tail_mass = float(np.sum(np.square(vectors[tail_start:, index])))
        rejected.append((index, values[index], tail_mass))

    scaling_values, scaling_vectors = np.linalg.eigh(jacobi)
    smooth = scaling_vectors @ np.diag(
        np.exp(-2 * tau * np.square(scaling_values))
    ) @ scaling_vectors.T
    accepted_vectors = vectors[:, accepted]
    trace = float(np.trace(accepted_vectors.T @ smooth @ accepted_vectors))
    maximum_tail = max((item[2] for item in rejected), default=0.0)
    return trace, len(accepted), maximum_tail


def run_probe():
    print("size lambda tau model trace accepted rejected delta")
    for size in (128, 192, 256, 384, 512):
        models = {
            "infinity": GUARDED.archimedean_jacobi(size),
            "p2": GUARDED.semilocal_jacobi(size, q=0.5),
        }
        for cutoff in (0.5, 1.0, 1.5):
            for tau in (0.05, 0.1, 0.2):
                results = {
                    name: one_sided_smoothed_trace(jacobi, cutoff, tau)
                    for name, jacobi in models.items()
                }
                delta = results["p2"][0] - results["infinity"][0]
                for name in ("infinity", "p2"):
                    trace, accepted, maximum_tail = results[name]
                    print(
                        f"{size:4d} {cutoff:4.1f} {tau:4.2f} {name:8s} "
                        f"{trace: .10e} {accepted:4d} {maximum_tail: .3e} "
                        f"{delta: .10e}"
                    )


if __name__ == "__main__":
    run_probe()
