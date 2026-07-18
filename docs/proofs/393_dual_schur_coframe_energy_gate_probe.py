"""Finite certificate for Proof 393's dual Schur-coframe energy."""

from __future__ import annotations

import argparse

import numpy as np


def positive_inverse_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 1e-12:
        raise ValueError("matrix is not strictly positive")
    return eigenvectors @ np.diag(eigenvalues**-0.5) @ eigenvectors.conj().T


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) < -1e-9:
        raise ValueError("matrix is not positive semidefinite")
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def orthogonal_complement(basis: np.ndarray) -> np.ndarray:
    _, _, right = np.linalg.svd(basis.conj().T, full_matrices=True)
    return right.conj().T[:, basis.shape[1] :]


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def normalized_schur_step(
    unitary: np.ndarray,
    basis: np.ndarray,
    coefficient: float,
) -> tuple[np.ndarray, np.ndarray]:
    size = unitary.shape[0]
    rank = basis.shape[1]
    complement = orthogonal_complement(basis)
    u_00 = basis.conj().T @ unitary @ basis
    u_01 = basis.conj().T @ unitary @ complement
    u_10 = complement.conj().T @ unitary @ basis
    u_11 = complement.conj().T @ unitary @ complement
    resolvent_times_u10 = np.linalg.solve(
        np.eye(size - rank, dtype=complex) - coefficient * u_11,
        u_10,
    )
    graph = coefficient * resolvent_times_u10
    transfer = u_00 + u_01 @ graph
    cosine = positive_inverse_square_root(
        np.eye(rank, dtype=complex) + graph.conj().T @ graph
    )
    sine = graph @ cosine
    next_basis = basis @ cosine + complement @ sine
    schur = (np.eye(rank) - coefficient * transfer) @ cosine
    return next_basis, schur / (1.0 + coefficient)


def schur_cohort(size: int, rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    source_raw = (
        rng.normal(size=(size, rank)) + 1j * rng.normal(size=(size, rank))
    )
    basis, _ = np.linalg.qr(source_raw)
    spectral_basis, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    frequencies = np.linspace(-1.4, 1.9, size)

    factors = []
    for prime in [2, 3, 5, 7, 11]:
        unitary = (
            spectral_basis
            @ np.diag(np.exp(1j * np.log(prime) * frequencies))
            @ spectral_basis.conj().T
        )
        basis, factor = normalized_schur_step(
            unitary,
            basis,
            prime**-0.5,
        )
        factors.append(factor)

    root_input = (
        rng.normal(size=(rank, rank + 2))
        + 1j * rng.normal(size=(rank, rank + 2))
    ) / np.sqrt(2.0 * rank)

    gamma = np.eye(rank, dtype=complex)
    delta_previous = np.eye(rank, dtype=complex)
    dual_square = np.zeros((rank, rank), dtype=complex)
    dual_energy = 0.0
    maximum_local_error = 0.0

    for factor in factors:
        defect = positive_square_root(
            np.eye(rank) - factor.conj().T @ factor
        )
        block = defect @ np.linalg.inv(factor) @ np.linalg.inv(gamma)
        gamma = gamma @ factor
        delta = np.linalg.inv(gamma).conj().T @ np.linalg.inv(gamma)
        maximum_local_error = max(
            maximum_local_error,
            relative_error(
                block.conj().T @ block,
                delta - delta_previous,
            ),
        )
        dual_square += block.conj().T @ block
        dual_energy += float(np.linalg.norm(block @ root_input, "fro") ** 2)
        delta_previous = delta

    expected_square = (
        np.linalg.inv(gamma).conj().T @ np.linalg.inv(gamma) - np.eye(rank)
    )
    expected_energy = (
        float(np.linalg.norm(np.linalg.inv(gamma) @ root_input, "fro") ** 2)
        - float(np.linalg.norm(root_input, "fro") ** 2)
    )

    return {
        "Schur maximum local dual error": maximum_local_error,
        "Schur dual telescope error": relative_error(
            dual_square,
            expected_square,
        ),
        "Schur root energy error": relative_error(dual_energy, expected_energy),
        "Schur forward cascade norm": float(np.linalg.norm(gamma, 2)),
        "Schur inverse cascade norm": float(np.linalg.norm(np.linalg.inv(gamma), 2)),
        "Schur dual root energy": dual_energy,
    }


def scalar_guard(prime_count: int) -> dict[str, float]:
    primes = [2, 3, 5, 7, 11, 13, 17, 19][:prime_count]
    gamma = 1.0
    energy = 0.0
    previous_inverse_square = 1.0
    maximum_error = 0.0
    maximum_local_inverse = 0.0

    for prime in primes:
        coefficient = prime**-0.5
        factor = (1.0 - coefficient) / (1.0 + coefficient)
        maximum_local_inverse = max(maximum_local_inverse, 1.0 / factor)
        defect = np.sqrt(1.0 - factor**2)
        block = defect / (factor * gamma)
        gamma *= factor
        inverse_square = gamma**-2
        maximum_error = max(
            maximum_error,
            abs(block**2 - (inverse_square - previous_inverse_square)),
        )
        energy += block**2
        previous_inverse_square = inverse_square

    expected = gamma**-2 - 1.0
    return {
        "scalar local identity error": maximum_error,
        "scalar telescope error": abs(energy - expected),
        "scalar maximum one-step inverse": maximum_local_inverse,
        "scalar complete inverse": 1.0 / gamma,
        "scalar dual energy": energy,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=6)
    parser.add_argument("--seed", type=int, default=393)
    parser.add_argument("--prime-count", type=int, default=8)
    parser.add_argument("--tolerance", type=float, default=2e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = schur_cohort(args.size, args.rank, args.seed)
    checks.update(scalar_guard(args.prime_count))
    print("Proof 393 dual Schur-coframe energy certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "Schur maximum local dual error",
        "Schur dual telescope error",
        "Schur root energy error",
        "scalar local identity error",
        "scalar telescope error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"dual Schur energy failed: {maximum_error:.3e}")
    if checks["scalar complete inverse"] <= checks["scalar maximum one-step inverse"]:
        raise RuntimeError("scalar guard has no cumulative inverse growth")
    if checks["scalar dual energy"] <= 1.0:
        raise RuntimeError("scalar dual energy guard is accidentally small")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("dual_schur_energy=INVERSE_GRAM_GROWTH")
    print("generic_dual_bessel_bound=REJECTED")
    print("corrected_root_stable_coframe=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
