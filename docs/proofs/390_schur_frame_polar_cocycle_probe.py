"""Finite certificate for Proof 390's Schur-frame polar cocycle."""

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
) -> dict[str, float]:
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
    graph_frame = basis @ cosine + complement @ sine

    denominator = np.eye(size, dtype=complex) - coefficient * unitary
    schur_frame = (
        np.eye(rank, dtype=complex) - coefficient * transfer
    ) @ cosine
    raw_inverse = np.linalg.solve(denominator, basis)
    schur_inverse = np.linalg.inv(schur_frame)
    raw_from_schur = graph_frame @ schur_inverse

    raw_gram = raw_inverse.conj().T @ raw_inverse
    schur_gram = schur_inverse.conj().T @ schur_inverse
    direct_polar = raw_inverse @ positive_inverse_square_root(raw_gram)
    polar_phase = schur_inverse @ positive_inverse_square_root(schur_gram)

    normalized_schur = schur_frame / (1.0 + coefficient)
    schur_defect = (
        np.eye(rank, dtype=complex)
        - normalized_schur.conj().T @ normalized_schur
    )
    plus_channel = (
        (np.eye(size, dtype=complex) + unitary) @ graph_frame
    )
    expected_defect = (
        coefficient
        / (1.0 + coefficient) ** 2
        * plus_channel.conj().T
        @ plus_channel
    )

    transfer_defect = np.eye(rank) - transfer.conj().T @ transfer
    graph_expected = (
        coefficient**2
        / (1.0 - coefficient**2)
        * transfer_defect
    )

    return {
        "graph identity error": relative_error(
            graph.conj().T @ graph,
            graph_expected,
        ),
        "graph frame isometry error": relative_error(
            graph_frame.conj().T @ graph_frame,
            np.eye(rank, dtype=complex),
        ),
        "Schur intertwining error": relative_error(
            denominator @ graph_frame,
            basis @ schur_frame,
        ),
        "raw inverse identity error": relative_error(
            raw_inverse,
            raw_from_schur,
        ),
        "raw Gram error": relative_error(raw_gram, schur_gram),
        "polar frame error": relative_error(
            direct_polar,
            graph_frame @ polar_phase,
        ),
        "polar phase unitary error": relative_error(
            polar_phase.conj().T @ polar_phase,
            np.eye(rank, dtype=complex),
        ),
        "normalized Schur defect error": relative_error(
            schur_defect,
            expected_defect,
        ),
        "normalized Schur positivity violation": max(
            0.0,
            -float(np.min(np.linalg.eigvalsh(schur_defect))),
        ),
        "polar versus Julia mismatch": float(
            np.linalg.norm(polar_phase - transfer, 2)
        ),
        "normalized Schur norm": float(np.linalg.norm(normalized_schur, 2)),
        "normalized Schur defect norm": float(np.linalg.norm(schur_defect, 2)),
    }


def certificate(size: int, rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    raw_basis = (
        rng.normal(size=(size, rank)) + 1j * rng.normal(size=(size, rank))
    )
    basis, _ = np.linalg.qr(raw_basis)
    spectral_basis, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    frequencies = np.linspace(-1.4, 1.9, size)

    checks_by_prime = []
    for prime in [2, 3, 5]:
        unitary = (
            spectral_basis
            @ np.diag(np.exp(1j * np.log(prime) * frequencies))
            @ spectral_basis.conj().T
        )
        checks_by_prime.append(one_step(unitary, basis, prime**-0.5))

    exact_labels = [
        "graph identity error",
        "graph frame isometry error",
        "Schur intertwining error",
        "raw inverse identity error",
        "raw Gram error",
        "polar frame error",
        "polar phase unitary error",
        "normalized Schur defect error",
        "normalized Schur positivity violation",
    ]
    result = {
        label: max(checks[label] for checks in checks_by_prime)
        for label in exact_labels
    }
    result.update(
        {
            "maximum polar versus Julia mismatch": max(
                checks["polar versus Julia mismatch"]
                for checks in checks_by_prime
            ),
            "maximum normalized Schur norm": max(
                checks["normalized Schur norm"] for checks in checks_by_prime
            ),
            "maximum normalized Schur defect norm": max(
                checks["normalized Schur defect norm"]
                for checks in checks_by_prime
            ),
        }
    )
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=14)
    parser.add_argument("--rank", type=int, default=5)
    parser.add_argument("--seed", type=int, default=390)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 390 Schur-frame polar cocycle certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "graph identity error",
        "graph frame isometry error",
        "Schur intertwining error",
        "raw inverse identity error",
        "raw Gram error",
        "polar frame error",
        "polar phase unitary error",
        "normalized Schur defect error",
        "normalized Schur positivity violation",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Schur-frame certificate failed: {maximum_error:.3e}")
    if checks["maximum polar versus Julia mismatch"] <= 1e-4:
        raise RuntimeError("polar and Julia coordinates accidentally coincide")
    if checks["maximum normalized Schur norm"] > 1.0 + args.tolerance:
        raise RuntimeError("normalized Schur frame is not contractive")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("physical_source_coordinate=SCHUR_FRAME")
    print("normalized_schur_frame=CONTRACTION")
    print("schur_defect_formula=EXACT")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
