"""First Euler/Szego variation of the prolate cross-spectral energy.

The archimedean Jacobi coefficients are exact.  Perturbing the measure by
1 + 2 a cos(L s) gives N'_0=[K_L,N], where K_L is the skew triangular part of
cos(L D).  This avoids reconstructing high semilocal moments.
"""

import numpy as np


def archimedean_scaling(size: int):
    indices = np.arange(size - 1, dtype=float)
    off_diagonal = 0.5 * np.sqrt((2 * indices + 1) * (2 * indices + 2))
    scaling = np.diag(off_diagonal, 1) + np.diag(off_diagonal, -1)
    return scaling, off_diagonal


def functional_calculus(matrix, function):
    values, vectors = np.linalg.eigh(matrix)
    return vectors @ np.diag(function(values)) @ vectors.T


def positive_projection(matrix, tail_tolerance=1e-2):
    values, vectors = np.linalg.eigh(matrix)
    candidates = vectors[:, values > 0]
    tail_start = 3 * matrix.shape[0] // 4
    tail_mass = np.sum(np.abs(candidates[tail_start:, :]) ** 2, axis=0)
    positive = candidates[:, tail_mass < tail_tolerance]
    return positive @ positive.T, positive.shape[1]


def cross_energy(projection, translation):
    rank = np.trace(projection)
    compressed = projection @ translation @ projection
    return float(np.real(rank - np.linalg.norm(compressed, "fro") ** 2))


def probe(size: int, cutoff: float, epsilon: float = 1e-5):
    scaling, off_diagonal = archimedean_scaling(size)
    grading = np.diag(np.arange(size, dtype=float))

    scaling_square = scaling @ scaling
    # Restore the path leaving and returning through the first omitted basis vector.
    tail_index = float(size - 1)
    tail_coefficient = 0.5 * np.sqrt(
        (2 * tail_index + 1) * (2 * tail_index + 2)
    )
    scaling_square[-1, -1] += tail_coefficient**2
    prolate = (
        -scaling_square
        + 2 * np.pi * cutoff**2 * (4 * grading + np.eye(size))
        - 0.25 * np.eye(size)
    )

    log_two = np.log(2.0)
    cosine = functional_calculus(scaling, lambda value: np.cos(log_two * value))
    row, column = np.indices((size, size))
    skew_sign = np.sign(row - column)
    generator = skew_sign * cosine
    grading_variation = generator @ grading - grading @ generator
    prolate_variation = 8 * np.pi * cutoff**2 * grading_variation

    projection_plus, rank_plus = positive_projection(
        prolate + epsilon * prolate_variation
    )
    projection_minus, rank_minus = positive_projection(
        prolate - epsilon * prolate_variation
    )
    if rank_plus != rank_minus:
        raise RuntimeError("epsilon crosses the positive spectral threshold")

    print(f"section={size} lambda={cutoff:.2f} rank={rank_plus}")
    for multiple in (0.5, 1.0, 1.5, 2.0, 3.0):
        translation = functional_calculus(
            scaling, lambda value: np.exp(1j * multiple * log_two * value)
        )
        energy_plus = cross_energy(projection_plus, translation)
        energy_minus = cross_energy(projection_minus, translation)
        derivative = (energy_plus - energy_minus) / (2 * epsilon)
        print(
            f"  r/log(2)={multiple:3.1f}  "
            f"dE/da={derivative: .9f}"
        )


for section_size in (96, 128, 192):
    for prolate_cutoff in (0.5, 1.0):
        probe(section_size, prolate_cutoff)
