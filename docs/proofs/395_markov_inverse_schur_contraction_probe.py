"""Finite certificate for Proof 395's Markov-inverse Schur contraction."""

from __future__ import annotations

import argparse

import numpy as np


def positive_inverse_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 1e-12:
        raise ValueError("matrix is not strictly positive")
    return eigenvectors @ np.diag(eigenvalues**-0.5) @ eigenvectors.conj().T


def orthogonal_complement(basis: np.ndarray) -> np.ndarray:
    _, _, right = np.linalg.svd(basis.conj().T, full_matrices=True)
    return right.conj().T[:, basis.shape[1] :]


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def one_step(
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
    forward = schur / (1.0 + coefficient)
    markov = (1.0 - coefficient) * np.linalg.inv(denominator)
    reverse = (1.0 - coefficient) * np.linalg.inv(schur)
    rho = (1.0 - coefficient) / (1.0 + coefficient)
    return {
        "next basis": next_basis,
        "denominator": denominator,
        "forward": forward,
        "markov": markov,
        "reverse": reverse,
        "rho": np.asarray(rho),
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
    frequencies = np.linspace(-1.7, 2.2, size)

    def translation(time: float) -> np.ndarray:
        return (
            spectral_basis
            @ np.diag(np.exp(1j * time * frequencies))
            @ spectral_basis.conj().T
        )

    current = source.copy()
    forward_product = np.eye(rank, dtype=complex)
    reverse_product = np.eye(rank, dtype=complex)
    ambient_markov_product = np.eye(size, dtype=complex)
    rho_product = 1.0
    maximum_intertwining_error = 0.0
    maximum_defect_error = 0.0
    maximum_pair_error = 0.0
    maximum_reverse_norm = 0.0
    reverse_factors = []

    for prime in [2, 3, 5, 7]:
        coefficient = prime**-0.5
        step = one_step(
            translation(np.log(prime)),
            current,
            coefficient,
        )
        reverse = step["reverse"]
        forward = step["forward"]
        markov = step["markov"]
        next_basis = step["next basis"]
        rho = float(step["rho"])

        maximum_intertwining_error = max(
            maximum_intertwining_error,
            relative_error(markov @ current, next_basis @ reverse),
        )
        source_defect = np.eye(rank) - reverse.conj().T @ reverse
        denominator = step["denominator"]
        minus_channel = (
            np.eye(size) - translation(np.log(prime))
        ) @ np.linalg.inv(denominator) @ current
        expected_defect = (
            coefficient * minus_channel.conj().T @ minus_channel
        )
        maximum_defect_error = max(
            maximum_defect_error,
            relative_error(source_defect, expected_defect),
        )
        maximum_pair_error = max(
            maximum_pair_error,
            relative_error(reverse @ forward, rho * np.eye(rank)),
            relative_error(forward @ reverse, rho * np.eye(rank)),
        )
        maximum_reverse_norm = max(
            maximum_reverse_norm,
            float(np.linalg.norm(reverse, 2)),
        )

        forward_product = forward_product @ forward
        reverse_product = reverse @ reverse_product
        ambient_markov_product = markov @ ambient_markov_product
        rho_product *= rho
        reverse_factors.append(reverse)
        current = next_basis

    complete_pair_error = max(
        relative_error(
            forward_product @ reverse_product,
            rho_product * np.eye(rank),
        ),
        relative_error(
            reverse_product @ forward_product,
            rho_product * np.eye(rank),
        ),
    )
    complete_markov_error = relative_error(
        ambient_markov_product @ source,
        current @ reverse_product,
    )

    defect_sum = np.zeros((rank, rank), dtype=complex)
    prefix = np.eye(rank, dtype=complex)
    for reverse in reverse_factors:
        defect = np.eye(rank) - reverse.conj().T @ reverse
        defect_sum += prefix.conj().T @ defect @ prefix
        prefix = reverse @ prefix
    defect_telescope_error = relative_error(
        defect_sum,
        np.eye(rank) - reverse_product.conj().T @ reverse_product,
    )

    return {
        "maximum Markov intertwining error": maximum_intertwining_error,
        "maximum minus defect error": maximum_defect_error,
        "maximum scalar pair error": maximum_pair_error,
        "complete scalar pair error": complete_pair_error,
        "complete Markov cascade error": complete_markov_error,
        "Markov defect telescope error": defect_telescope_error,
        "maximum reverse factor norm": maximum_reverse_norm,
        "complete reverse cascade norm": float(np.linalg.norm(reverse_product, 2)),
        "forward inverse norm": float(np.linalg.norm(np.linalg.inv(forward_product), 2)),
        "rho product": rho_product,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=6)
    parser.add_argument("--seed", type=int, default=395)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 395 Markov-inverse Schur contraction certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum Markov intertwining error",
        "maximum minus defect error",
        "maximum scalar pair error",
        "complete scalar pair error",
        "complete Markov cascade error",
        "Markov defect telescope error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Markov Schur certificate failed: {maximum_error:.3e}")
    if checks["maximum reverse factor norm"] > 1.0 + args.tolerance:
        raise RuntimeError("source Markov transition is not contractive")
    if checks["complete reverse cascade norm"] > 1.0 + args.tolerance:
        raise RuntimeError("complete Markov cascade is not contractive")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("source_markov_inverse=CONTRACTION")
    print("minus_channel_defect=EXACT")
    print("forward_inverse_pair=SCALAR")
    print("scale_invariant_relative_numerator=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
