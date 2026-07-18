"""Finite certificate for Proof 396's bi-Schur relative numerator."""

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
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float]:
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
    forward = schur / (1.0 + coefficient)
    reverse = (1.0 - coefficient) * np.linalg.inv(schur)
    rho = (1.0 - coefficient) / (1.0 + coefficient)
    return next_basis, forward, reverse, rho


def certificate(size: int, rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    source_raw = (
        rng.normal(size=(size, rank)) + 1j * rng.normal(size=(size, rank))
    )
    source, _ = np.linalg.qr(source_raw)
    spectral_basis, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    frequencies = np.linspace(-1.5, 2.1, size)

    def translation(time: float) -> np.ndarray:
        return (
            spectral_basis
            @ np.diag(np.exp(1j * time * frequencies))
            @ spectral_basis.conj().T
        )

    detector = (
        spectral_basis
        @ np.diag(0.3 + rng.random(size))
        @ spectral_basis.conj().T
    )

    bases = [source]
    forwards = []
    reverses = []
    rhos = []
    alphas = [source.conj().T @ detector @ source]
    for prime in [2, 3, 5, 7]:
        next_basis, forward, reverse, rho = one_step(
            translation(np.log(prime)),
            bases[-1],
            prime**-0.5,
        )
        bases.append(next_basis)
        forwards.append(forward)
        reverses.append(reverse)
        rhos.append(rho)
        alphas.append(next_basis.conj().T @ detector @ next_basis)

    gamma = np.eye(rank, dtype=complex)
    lamb = np.eye(rank, dtype=complex)
    rho_product = 1.0
    for forward, reverse, rho in zip(forwards, reverses, rhos, strict=True):
        gamma = gamma @ forward
        lamb = reverse @ lamb
        rho_product *= rho

    numerator = gamma @ alphas[-1] @ lamb - rho_product * alphas[0]
    ordered = gamma @ alphas[-1] @ np.linalg.inv(gamma) - alphas[0]
    reverse_ordered = np.linalg.inv(lamb) @ alphas[-1] @ lamb - alphas[0]

    maximum_local_error = 0.0
    local_relative = []
    for index, (forward, reverse, rho) in enumerate(
        zip(forwards, reverses, rhos, strict=True)
    ):
        old_alpha = alphas[index]
        new_alpha = alphas[index + 1]
        forward_defect = forward @ new_alpha - old_alpha @ forward
        relative_defect = forward @ new_alpha @ reverse - rho * old_alpha
        maximum_local_error = max(
            maximum_local_error,
            relative_error(relative_defect, forward_defect @ reverse),
        )
        local_relative.append(relative_defect)

    telescoped = np.zeros((rank, rank), dtype=complex)
    gamma_prefix = np.eye(rank, dtype=complex)
    lambda_prefix = np.eye(rank, dtype=complex)
    for index, relative_defect in enumerate(local_relative):
        rho_after = float(np.prod(rhos[index + 1 :]))
        telescoped += (
            rho_after
            * gamma_prefix
            @ relative_defect
            @ lambda_prefix
        )
        gamma_prefix = gamma_prefix @ forwards[index]
        lambda_prefix = reverses[index] @ lambda_prefix

    scalar_numerator = (
        gamma @ np.eye(rank) @ lamb - rho_product * np.eye(rank)
    )
    ambient_response = np.trace(
        detector
        @ (
            bases[-1] @ bases[-1].conj().T
            - source @ source.conj().T
        )
    )

    return {
        "forward reverse scalar pair error": max(
            relative_error(gamma @ lamb, rho_product * np.eye(rank)),
            relative_error(lamb @ gamma, rho_product * np.eye(rank)),
        ),
        "ordered relative numerator error": relative_error(
            ordered,
            numerator / rho_product,
        ),
        "reverse ordered response error": relative_error(
            ordered,
            reverse_ordered,
        ),
        "maximum local relative defect error": maximum_local_error,
        "relative numerator telescope error": relative_error(
            numerator,
            telescoped,
        ),
        "scalar channel numerator norm": float(np.linalg.norm(scalar_numerator, 2)),
        "finite ambient trace error": relative_error(
            np.trace(ordered),
            ambient_response,
        ),
        "rho product": rho_product,
        "relative numerator norm": float(np.linalg.norm(numerator, 2)),
        "ordered response magnitude": float(abs(np.trace(ordered))),
        "forward cascade norm": float(np.linalg.norm(gamma, 2)),
        "reverse cascade norm": float(np.linalg.norm(lamb, 2)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=6)
    parser.add_argument("--seed", type=int, default=396)
    parser.add_argument("--tolerance", type=float, default=2e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 396 bi-Schur relative numerator certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "forward reverse scalar pair error",
        "ordered relative numerator error",
        "reverse ordered response error",
        "maximum local relative defect error",
        "relative numerator telescope error",
        "scalar channel numerator norm",
        "finite ambient trace error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"bi-Schur numerator failed: {maximum_error:.3e}")
    if checks["forward cascade norm"] > 1.0 + args.tolerance:
        raise RuntimeError("forward Schur cascade is not contractive")
    if checks["reverse cascade norm"] > 1.0 + args.tolerance:
        raise RuntimeError("inverse Markov cascade is not contractive")
    if checks["ordered response magnitude"] <= 1e-6:
        raise RuntimeError("ordered response is accidentally trivial")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("bischur_relative_numerator=EXACT")
    print("coherent_scalar_channel=CANCELS")
    print("uniform_rho_relative_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
