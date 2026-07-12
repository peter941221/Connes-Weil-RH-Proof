"""Fixed p=2 Jacobi coefficients from modified Gaussian quadrature.

The archimedean Jacobi section supplies Gauss nodes and weights.  Multiplying
those weights by the exact Euler density and rerunning Lanczos avoids Hankel
moment conditioning.  Run with SciPy; the WSL base environment lacks it.
"""

import numpy as np
from scipy.linalg import eigh_tridiagonal


def archimedean_gauss(section_size: int):
    indices = np.arange(section_size - 1, dtype=float)
    off_diagonal = 0.5 * np.sqrt((2 * indices + 1) * (2 * indices + 2))
    diagonal = np.zeros(section_size)
    nodes, eigenvectors = eigh_tridiagonal(diagonal, off_diagonal)
    weights = np.square(eigenvectors[0, :])
    return nodes, weights


def modified_recurrence(nodes, weights, degree: int):
    basis = np.zeros((nodes.size, degree + 1))
    current = np.sqrt(weights / weights.sum())
    basis[:, 0] = current
    diagonal = np.zeros(degree)
    off_diagonal = np.zeros(degree)

    for index in range(degree):
        residual = nodes * current
        diagonal[index] = np.dot(current, residual)
        residual -= diagonal[index] * current
        active = basis[:, : index + 1]
        for _ in range(2):
            residual -= active @ (active.T @ residual)
        beta = np.linalg.norm(residual)
        off_diagonal[index] = beta
        current = residual / beta
        basis[:, index + 1] = current

    return diagonal, off_diagonal


sample_indices = (4, 8, 12, 16, 20, 24)
for section in (64, 96, 128):
    nodes, base_weights = archimedean_gauss(section)
    _, recovered_base = modified_recurrence(
        nodes, base_weights, degree=max(sample_indices) + 1
    )
    expected_base = np.array(
        [
            0.5 * np.sqrt((2 * index + 1) * (2 * index + 2))
            for index in range(max(sample_indices) + 1)
        ]
    )
    base_error = np.max(np.abs(recovered_base - expected_base))
    if base_error > 1e-8:
        print(
            f"gauss_section={section} rejected: "
            f"base recurrence error={base_error:.3e}"
        )
        continue
    a = 2**-0.5
    euler_density = 1 / np.abs(
        1 - a * np.exp(-1j * np.log(2.0) * nodes)
    ) ** 2
    _, semilocal = modified_recurrence(
        nodes, base_weights * euler_density, degree=max(sample_indices) + 1
    )
    print(f"gauss_section={section}")
    for index in sample_indices:
        archimedean = 0.5 * np.sqrt((2 * index + 1) * (2 * index + 2))
        difference = semilocal[index] - archimedean
        print(
            f"  n={index:3d}  a_p-a_inf={difference: .10f}  "
            f"difference/sqrt(n)={difference / np.sqrt(index): .10f}"
        )
