"""Finite certificate for Proof 392's Schur co-defect insertion."""

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


def graph_step(
    unitary: np.ndarray,
    basis: np.ndarray,
    coefficient: float,
) -> dict[str, np.ndarray]:
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
    denominator = np.eye(size, dtype=complex) - coefficient * unitary
    normalized_ambient = denominator / (1.0 + coefficient)
    schur = (np.eye(rank) - coefficient * transfer) @ cosine
    normalized_schur = schur / (1.0 + coefficient)
    return {
        "next basis": next_basis,
        "normalized ambient": normalized_ambient,
        "normalized Schur": normalized_schur,
    }


def certificate(size: int, rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    source_raw = (
        rng.normal(size=(size, rank)) + 1j * rng.normal(size=(size, rank))
    )
    source, _ = np.linalg.qr(source_raw)
    spectral_basis, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    frequencies = np.linspace(-1.5, 1.8, size)

    def translation(time: float) -> np.ndarray:
        return (
            spectral_basis
            @ np.diag(np.exp(1j * time * frequencies))
            @ spectral_basis.conj().T
        )

    detector = (
        spectral_basis
        @ np.diag(0.2 + rng.random(size))
        @ spectral_basis.conj().T
    )

    primes = [2, 3, 5, 7]
    bases = [source]
    factors = []
    ambient_factors = []
    alphas = [source.conj().T @ detector @ source]

    for prime in primes:
        step = graph_step(
            translation(np.log(prime)),
            bases[-1],
            prime**-0.5,
        )
        bases.append(step["next basis"])
        factors.append(step["normalized Schur"])
        ambient_factors.append(step["normalized ambient"])
        alphas.append(bases[-1].conj().T @ detector @ bases[-1])

    local_defects = []
    boundary_factors = []
    maximum_local_error = 0.0
    maximum_codefect_error = 0.0
    maximum_douglas_error = 0.0
    maximum_douglas_norm = 0.0

    for index, factor in enumerate(factors):
        old_basis = bases[index]
        new_basis = bases[index + 1]
        ambient = ambient_factors[index]
        old_alpha = alphas[index]
        new_alpha = alphas[index + 1]
        new_projection = new_basis @ new_basis.conj().T
        complement_projection = np.eye(size) - new_projection

        local_defect = factor @ new_alpha - old_alpha @ factor
        crossing = complement_projection @ detector @ new_basis
        boundary = old_basis.conj().T @ ambient @ crossing
        maximum_local_error = max(
            maximum_local_error,
            relative_error(local_defect, -boundary),
        )

        rectangular = old_basis.conj().T @ ambient @ complement_projection
        left_defect_sq = np.eye(rank) - factor @ factor.conj().T
        ambient_loss = (
            old_basis.conj().T
            @ (np.eye(size) - ambient @ ambient.conj().T)
            @ old_basis
        )
        maximum_codefect_error = max(
            maximum_codefect_error,
            relative_error(
                left_defect_sq,
                ambient_loss + rectangular @ rectangular.conj().T,
            ),
        )

        left_defect = positive_square_root(left_defect_sq)
        douglas = np.linalg.pinv(left_defect, rcond=1e-11) @ rectangular
        maximum_douglas_error = max(
            maximum_douglas_error,
            relative_error(rectangular, left_defect @ douglas),
        )
        maximum_douglas_norm = max(
            maximum_douglas_norm,
            float(np.linalg.norm(douglas, 2)),
        )
        boundary_factor = douglas @ detector @ new_basis
        maximum_douglas_error = max(
            maximum_douglas_error,
            relative_error(local_defect, -left_defect @ boundary_factor),
        )
        local_defects.append(local_defect)
        boundary_factors.append(boundary_factor)

    gamma = np.eye(rank, dtype=complex)
    prefixes = [gamma]
    for factor in factors:
        gamma = gamma @ factor
        prefixes.append(gamma)

    global_defect = gamma @ alphas[-1] - alphas[0] @ gamma
    telescoped = np.zeros((rank, rank), dtype=complex)
    codefect_left = []
    boundary_right = []
    for index, local_defect in enumerate(local_defects):
        suffix = np.eye(rank, dtype=complex)
        for factor in factors[index + 1 :]:
            suffix = suffix @ factor
        telescoped += prefixes[index] @ local_defect @ suffix

        left_defect = positive_square_root(
            np.eye(rank) - factors[index] @ factors[index].conj().T
        )
        codefect_left.append(prefixes[index] @ left_defect)
        boundary_right.append(boundary_factors[index] @ suffix)

    left_row = np.hstack(codefect_left)
    right_column = np.vstack(boundary_right)
    factored_global = -left_row @ right_column
    codefect_sum = left_row @ left_row.conj().T
    expected_codefect = np.eye(rank) - gamma @ gamma.conj().T

    ordered = global_defect @ np.linalg.inv(gamma)
    local_similarity = np.zeros((rank, rank), dtype=complex)
    for index, local_defect in enumerate(local_defects):
        local_similarity += (
            prefixes[index]
            @ local_defect
            @ np.linalg.inv(factors[index])
            @ np.linalg.inv(prefixes[index])
        )

    return {
        "maximum local defect error": maximum_local_error,
        "maximum co-defect decomposition error": maximum_codefect_error,
        "maximum Douglas reconstruction error": maximum_douglas_error,
        "global intertwinement telescope error": relative_error(
            global_defect,
            telescoped,
        ),
        "global co-defect factorization error": relative_error(
            global_defect,
            factored_global,
        ),
        "co-defect row identity error": relative_error(
            codefect_sum,
            expected_codefect,
        ),
        "ordered local similarity error": relative_error(
            ordered,
            local_similarity,
        ),
        "maximum Douglas contraction norm": maximum_douglas_norm,
        "co-defect row norm": float(np.linalg.norm(left_row, 2)),
        "remaining boundary column norm": float(np.linalg.norm(right_column, 2)),
        "normalized inverse norm": float(np.linalg.norm(np.linalg.inv(gamma), 2)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=6)
    parser.add_argument("--seed", type=int, default=392)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 392 Schur detector co-defect insertion certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum local defect error",
        "maximum co-defect decomposition error",
        "maximum Douglas reconstruction error",
        "global intertwinement telescope error",
        "global co-defect factorization error",
        "co-defect row identity error",
        "ordered local similarity error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Schur co-defect insertion failed: {maximum_error:.3e}")
    if checks["maximum Douglas contraction norm"] > 1.0 + args.tolerance:
        raise RuntimeError("Douglas readout is not contractive")
    if checks["co-defect row norm"] > 1.0 + args.tolerance:
        raise RuntimeError("co-defect history row is not contractive")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("moving_detector_defect=SCHUR_CODEFECT_FACTOR")
    print("complete_prefix_history=CONTRACTIVE_ROW")
    print("cumulative_condition_number=ABSENT_BEFORE_ANOMALY")
    print("compact_root_suffix_column=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
