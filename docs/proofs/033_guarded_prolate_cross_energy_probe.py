"""Guarded prolate cross-energy probe from the exact Lambert Gram matrix.

The old probe reconstructed recurrence coefficients from continuous
quadrature and suffered moment/Lanczos instability.  This version obtains the
Jacobi coefficients from exact Meixner--Lambert Gram Cholesky pivots.  A
positive prolate eigenvector is accepted only when its mass in the final
quarter of the finite section is below the stated tail tolerance.

This is route screening, not evidence for self-adjointness or convergence.
"""

import importlib.util
from pathlib import Path

import numpy as np


def load_schur_probe():
    path = Path(__file__).with_name("031_fixed_q_schur_probe.py")
    specification = importlib.util.spec_from_file_location("schur_probe", path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


SCHUR = load_schur_probe()


def semilocal_jacobi(size: int, q: float, layers: int = 40):
    _, even_gram = SCHUR.parity_gram(size - 1, q, 0, layers)
    _, odd_gram = SCHUR.parity_gram(size - 1, q, 1, layers)
    even_pivots = np.square(np.diag(np.linalg.cholesky(even_gram)))
    odd_pivots = np.square(np.diag(np.linalg.cholesky(odd_gram)))
    pivots = np.empty(size)
    pivots[0::2] = even_pivots
    pivots[1::2] = odd_pivots
    degrees = np.arange(size - 1, dtype=float)
    archimedean = np.sqrt((degrees + 0.5) * (degrees + 1))
    off_diagonal = archimedean * np.sqrt(pivots[1:] / pivots[:-1])
    jacobi = np.diag(off_diagonal, 1) + np.diag(off_diagonal, -1)
    return jacobi


def archimedean_jacobi(size: int):
    degrees = np.arange(size - 1, dtype=float)
    off_diagonal = np.sqrt((degrees + 0.5) * (degrees + 1))
    return np.diag(off_diagonal, 1) + np.diag(off_diagonal, -1)


def guarded_positive_projection(
    jacobi: np.ndarray,
    cutoff: float,
    tail_fraction: float = 0.25,
    tail_tolerance: float = 1e-9,
):
    size = jacobi.shape[0]
    grading = np.diag(np.arange(size, dtype=float))
    prolate = (
        -(jacobi @ jacobi)
        + 2 * np.pi * cutoff**2 * (4 * grading + np.eye(size))
        - 0.25 * np.eye(size)
    )
    values, vectors = np.linalg.eigh(prolate)
    tail_start = int((1 - tail_fraction) * size)
    positive_indices = np.flatnonzero(values > 0)
    accepted = []
    rejected = []
    for index in positive_indices:
        tail_mass = np.sum(np.square(vectors[tail_start:, index]))
        if tail_mass <= tail_tolerance:
            accepted.append(index)
        else:
            rejected.append((index, values[index], tail_mass))
    return values, vectors[:, accepted], rejected


def cross_energy(jacobi: np.ndarray, positive_vectors: np.ndarray, samples):
    scaling_values, scaling_vectors = np.linalg.eigh(jacobi)
    energies = []
    for sample in samples:
        translation = scaling_vectors @ np.diag(
            np.exp(1j * sample * scaling_values)
        ) @ scaling_vectors.T
        compression = positive_vectors.T @ translation @ positive_vectors
        energy = positive_vectors.shape[1] - np.linalg.norm(compression, "fro") ** 2
        energies.append(float(np.real(energy)))
    return np.array(energies)


def run_probe():
    q = 0.5
    log_two = np.log(2.0)
    samples = log_two * np.array([0.0, 0.5, 1.0, 1.5, 2.0, 3.0])
    print("size lambda model accepted rejected min_pos max_tail energy_samples")
    for size in (128, 192, 256, 384):
        models = {
            "infinity": archimedean_jacobi(size),
            "p2": semilocal_jacobi(size, q),
        }
        for cutoff in (0.5, 1.0, 1.5, 2.0):
            for name, jacobi in models.items():
                values, positive, rejected = guarded_positive_projection(
                    jacobi, cutoff
                )
                energies = cross_energy(jacobi, positive, samples)
                minimum_positive = (
                    np.min(values[values > 0]) if np.any(values > 0) else np.nan
                )
                maximum_rejected_tail = max(
                    (item[2] for item in rejected), default=0.0
                )
                rendered = ",".join(f"{value:.8f}" for value in energies)
                print(
                    f"{size:4d} {cutoff:4.1f} {name:8s} "
                    f"{positive.shape[1]:3d} {len(rejected):3d} "
                    f"{minimum_positive: .3e} {maximum_rejected_tail:.3e} "
                    f"{rendered}"
                )


if __name__ == "__main__":
    run_probe()
