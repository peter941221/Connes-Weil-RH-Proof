"""Probe the S={infinity,2} semilocal prolate trace kernel.

The finite Jacobi section is obtained by Lanczos tridiagonalization of the
scaling multiplier against the Euler-weighted spectral measure.  This is only
numerical route screening; it does not prove self-adjointness or convergence.
"""

import numpy as np


def log_gamma_lanczos(values):
    coefficients = np.array(
        [
            0.99999999999980993,
            676.5203681218851,
            -1259.1392167224028,
            771.32342877765313,
            -176.61502916214059,
            12.507343278686905,
            -0.13857109526572012,
            9.9843695780195716e-6,
            1.5056327351493116e-7,
        ]
    )
    shifted = values - 1
    series = np.full_like(values, coefficients[0], dtype=complex)
    for index, coefficient in enumerate(coefficients[1:], start=1):
        series += coefficient / (shifted + index)
    t = shifted + 7.5
    return (
        0.5 * np.log(2 * np.pi)
        + (shifted + 0.5) * np.log(t)
        - t
        + np.log(series)
    )


def spectral_quadrature(point_count: int = 20001, radius: float = 80.0):
    points = np.linspace(-radius, radius, point_count)
    step = points[1] - points[0]
    gamma_arguments = 0.25 + 0.5j * points
    gamma_weight = np.exp(2 * np.real(log_gamma_lanczos(gamma_arguments)))
    a = 2**-0.5
    euler_weight = 1 / np.abs(1 - a * np.exp(1j * points * np.log(2.0))) ** 2
    weights = gamma_weight * euler_weight * step
    weights /= weights.sum()
    return points, weights


def jacobi_from_measure(points, weights, size: int):
    current = np.sqrt(weights)
    basis = []
    diagonal = np.zeros(size)
    off_diagonal = np.zeros(size - 1)

    for index in range(size):
        basis.append(current.copy())
        residual = points * current
        diagonal[index] = np.dot(current, residual)
        residual -= diagonal[index] * current
        for _ in range(2):
            for vector in basis:
                residual -= np.dot(vector, residual) * vector
        if index + 1 == size:
            break
        beta = np.linalg.norm(residual)
        off_diagonal[index] = beta
        current = residual / beta

    jacobi = np.diag(diagonal)
    jacobi += np.diag(off_diagonal, 1) + np.diag(off_diagonal, -1)
    return jacobi


def cross_spectral_energy(jacobi, cutoff: float, samples):
    size = jacobi.shape[0]
    grading = np.diag(np.arange(size, dtype=float))
    prolate = (
        -(jacobi @ jacobi)
        + 2 * np.pi * cutoff**2 * (4 * grading + np.eye(size))
        - 0.25 * np.eye(size)
    )
    _, prolate_vectors = np.linalg.eigh(prolate)
    prolate_values = np.linalg.eigvalsh(prolate)
    positive = prolate_vectors[:, prolate_values > 0]
    projection = positive @ positive.T

    scaling_values, scaling_vectors = np.linalg.eigh(jacobi)
    energies = []
    for value in samples:
        translation = scaling_vectors @ np.diag(
            np.exp(1j * value * scaling_values)
        ) @ scaling_vectors.T
        compressed = positive.T @ translation @ positive
        energy = positive.shape[1] - np.linalg.norm(compressed, "fro") ** 2
        energies.append(float(np.real(energy)))
    return positive.shape[1], np.array(energies)


points, weights = spectral_quadrature()
log_two = np.log(2.0)
samples = np.array(
    [0.0, 0.5 * log_two, log_two, 1.5 * log_two, 2 * log_two, 3 * log_two]
)

for size in (16, 24, 32):
    jacobi = jacobi_from_measure(points, weights, size=size)
    print(f"section={size} last off-diagonals={np.diag(jacobi, 1)[-3:]}")
    for cutoff in (0.5, 1.0):
        rank, energies = cross_spectral_energy(jacobi, cutoff, samples)
        normalized = energies / rank
        values = ", ".join(f"{value:.6f}" for value in normalized)
        print(f"  lambda={cutoff:.1f} rank={rank} cross_energy/rank={values}")
