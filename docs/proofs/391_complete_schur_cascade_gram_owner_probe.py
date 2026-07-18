"""Finite certificate for Proof 391's complete Schur cascade."""

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
    schur = (np.eye(rank) - coefficient * transfer) @ cosine
    normalized = schur / (1.0 + coefficient)
    return {
        "next basis": next_basis,
        "denominator": denominator,
        "Schur": schur,
        "normalized Schur": normalized,
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
    frequencies = np.linspace(-1.6, 2.0, size)

    def translation(time: float) -> np.ndarray:
        return (
            spectral_basis
            @ np.diag(np.exp(1j * time * frequencies))
            @ spectral_basis.conj().T
        )

    detector_values = 0.3 + rng.random(size)
    detector = (
        spectral_basis
        @ np.diag(detector_values)
        @ spectral_basis.conj().T
    )

    primes = [2, 3, 5, 7]
    current_basis = source.copy()
    denominator_product = np.eye(size, dtype=complex)
    schur_product = np.eye(rank, dtype=complex)
    gamma_product = np.eye(rank, dtype=complex)
    scalar_product = 1.0
    normalized_factors = []
    maximum_local_error = 0.0

    for prime in primes:
        coefficient = prime**-0.5
        step = graph_step(
            translation(np.log(prime)),
            current_basis,
            coefficient,
        )
        maximum_local_error = max(
            maximum_local_error,
            relative_error(
                step["denominator"] @ step["next basis"],
                current_basis @ step["Schur"],
            ),
        )
        denominator_product = denominator_product @ step["denominator"]
        schur_product = schur_product @ step["Schur"]
        gamma_product = gamma_product @ step["normalized Schur"]
        scalar_product *= 1.0 + coefficient
        normalized_factors.append(step["normalized Schur"])
        current_basis = step["next basis"]

    complete_intertwining_error = relative_error(
        denominator_product @ current_basis,
        source @ schur_product,
    )
    raw_inverse = np.linalg.solve(denominator_product, source)
    raw_from_schur = current_basis @ np.linalg.inv(schur_product)
    raw_inverse_error = relative_error(raw_inverse, raw_from_schur)

    metric = raw_inverse.conj().T @ raw_inverse
    expected_metric = (
        np.linalg.inv(schur_product).conj().T
        @ np.linalg.inv(schur_product)
    )
    metric_error = relative_error(metric, expected_metric)
    normalized_frame = raw_inverse @ positive_inverse_square_root(metric)
    projection_error = relative_error(
        normalized_frame @ normalized_frame.conj().T,
        current_basis @ current_basis.conj().T,
    )
    scalar_normalization_error = relative_error(
        schur_product,
        scalar_product * gamma_product,
    )

    co_defect_sum = np.zeros((rank, rank), dtype=complex)
    prefix = np.eye(rank, dtype=complex)
    for factor in normalized_factors:
        left_defect_sq = np.eye(rank) - factor @ factor.conj().T
        co_defect_sum += prefix @ left_defect_sq @ prefix.conj().T
        prefix = prefix @ factor
    co_defect_error = relative_error(
        co_defect_sum,
        np.eye(rank) - gamma_product @ gamma_product.conj().T,
    )

    input_defect_sum = np.zeros((rank, rank), dtype=complex)
    suffix = np.eye(rank, dtype=complex)
    for factor in reversed(normalized_factors):
        defect_sq = np.eye(rank) - factor.conj().T @ factor
        input_defect_sum += suffix.conj().T @ defect_sq @ suffix
        suffix = factor @ suffix
    input_defect_error = relative_error(
        input_defect_sum,
        np.eye(rank) - gamma_product.conj().T @ gamma_product,
    )

    alpha_zero = source.conj().T @ detector @ source
    alpha_final = current_basis.conj().T @ detector @ current_basis
    numerator = raw_inverse.conj().T @ detector @ raw_inverse
    ordered_response = (
        np.linalg.inv(metric) @ numerator - alpha_zero
    )
    schur_response = (
        schur_product
        @ alpha_final
        @ np.linalg.inv(schur_product)
        - alpha_zero
    )
    gamma_response = (
        gamma_product
        @ alpha_final
        @ np.linalg.inv(gamma_product)
        - alpha_zero
    )
    ambient_response = np.trace(
        detector
        @ (
            current_basis @ current_basis.conj().T
            - source @ source.conj().T
        )
    )

    return {
        "maximum local intertwining error": maximum_local_error,
        "complete intertwining error": complete_intertwining_error,
        "raw inverse product error": raw_inverse_error,
        "compressed metric error": metric_error,
        "Gram projection error": projection_error,
        "scalar normalization error": scalar_normalization_error,
        "co-defect telescope error": co_defect_error,
        "input-defect telescope error": input_defect_error,
        "ordered Schur response error": relative_error(
            ordered_response,
            schur_response,
        ),
        "normalized Schur response error": relative_error(
            ordered_response,
            gamma_response,
        ),
        "finite trace readback error": relative_error(
            np.trace(ordered_response),
            ambient_response,
        ),
        "normalized cascade norm": float(np.linalg.norm(gamma_product, 2)),
        "normalized inverse norm": float(
            np.linalg.norm(np.linalg.inv(gamma_product), 2)
        ),
        "response magnitude": float(abs(np.trace(ordered_response))),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=6)
    parser.add_argument("--seed", type=int, default=391)
    parser.add_argument("--tolerance", type=float, default=8e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 391 complete Schur-cascade Gram certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum local intertwining error",
        "complete intertwining error",
        "raw inverse product error",
        "compressed metric error",
        "Gram projection error",
        "scalar normalization error",
        "co-defect telescope error",
        "input-defect telescope error",
        "ordered Schur response error",
        "normalized Schur response error",
        "finite trace readback error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"complete Schur cascade failed: {maximum_error:.3e}")
    if checks["normalized cascade norm"] > 1.0 + args.tolerance:
        raise RuntimeError("normalized Schur cascade is not contractive")
    if checks["response magnitude"] <= 1e-6:
        raise RuntimeError("finite response is accidentally trivial")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("proof_343_gram_owner=SCHUR_CASCADE")
    print("forward_reverse_defect_rows=CONTRACTIVE")
    print("ordered_similarity_anomaly=RETAINED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
