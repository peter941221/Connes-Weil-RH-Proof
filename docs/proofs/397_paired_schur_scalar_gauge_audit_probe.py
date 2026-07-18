"""Finite certificate for Proof 397's paired scalar-gauge audit."""

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
    graph = coefficient * np.linalg.solve(
        np.eye(size - rank, dtype=complex) - coefficient * u_11,
        u_10,
    )
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
    frequencies = np.linspace(-1.7, 2.3, size)

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

    bases = [source]
    forwards = []
    reverses = []
    rhos = []
    alphas = [source.conj().T @ detector @ source]
    primes = [2, 3, 5, 7]
    for prime in primes:
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

    gauges = [0.43, 1.61, 0.72, 1.37]
    gauged_forwards = [
        gauge * forward
        for gauge, forward in zip(gauges, forwards, strict=True)
    ]
    gauged_reverses = [
        reverse / gauge
        for gauge, reverse in zip(gauges, reverses, strict=True)
    ]

    gamma = np.eye(rank, dtype=complex)
    lamb = np.eye(rank, dtype=complex)
    gauged_gamma = np.eye(rank, dtype=complex)
    gauged_lambda = np.eye(rank, dtype=complex)
    rho_product = 1.0
    for forward, reverse, gauged_forward, gauged_reverse, rho in zip(
        forwards,
        reverses,
        gauged_forwards,
        gauged_reverses,
        rhos,
        strict=True,
    ):
        gamma = gamma @ forward
        lamb = reverse @ lamb
        gauged_gamma = gauged_gamma @ gauged_forward
        gauged_lambda = gauged_reverse @ gauged_lambda
        rho_product *= rho

    gauge_product = float(np.prod(gauges))
    numerator = gamma @ alphas[-1] @ lamb - rho_product * alphas[0]
    gauged_numerator = (
        gauged_gamma @ alphas[-1] @ gauged_lambda
        - rho_product * alphas[0]
    )
    ordered = gamma @ alphas[-1] @ np.linalg.inv(gamma) - alphas[0]
    gauged_ordered = (
        gauged_gamma @ alphas[-1] @ np.linalg.inv(gauged_gamma)
        - alphas[0]
    )

    maximum_step_pair_error = 0.0
    maximum_local_invariance_error = 0.0
    local_relative = []
    gauged_local_relative = []
    for index, (forward, reverse, gauged_forward, gauged_reverse, rho) in enumerate(
        zip(
            forwards,
            reverses,
            gauged_forwards,
            gauged_reverses,
            rhos,
            strict=True,
        )
    ):
        identity = np.eye(rank, dtype=complex)
        maximum_step_pair_error = max(
            maximum_step_pair_error,
            relative_error(gauged_forward @ gauged_reverse, rho * identity),
            relative_error(gauged_reverse @ gauged_forward, rho * identity),
        )
        old_alpha = alphas[index]
        new_alpha = alphas[index + 1]
        local = forward @ new_alpha @ reverse - rho * old_alpha
        gauged_local = (
            gauged_forward @ new_alpha @ gauged_reverse - rho * old_alpha
        )
        maximum_local_invariance_error = max(
            maximum_local_invariance_error,
            relative_error(gauged_local, local),
        )
        local_relative.append(local)
        gauged_local_relative.append(gauged_local)

    telescope = np.zeros((rank, rank), dtype=complex)
    gauged_telescope = np.zeros((rank, rank), dtype=complex)
    gamma_prefix = np.eye(rank, dtype=complex)
    lambda_prefix = np.eye(rank, dtype=complex)
    gauged_gamma_prefix = np.eye(rank, dtype=complex)
    gauged_lambda_prefix = np.eye(rank, dtype=complex)
    for index, (local, gauged_local) in enumerate(
        zip(local_relative, gauged_local_relative, strict=True)
    ):
        rho_after = float(np.prod(rhos[index + 1 :]))
        telescope += rho_after * gamma_prefix @ local @ lambda_prefix
        gauged_telescope += (
            rho_after
            * gauged_gamma_prefix
            @ gauged_local
            @ gauged_lambda_prefix
        )
        gamma_prefix = gamma_prefix @ forwards[index]
        lambda_prefix = reverses[index] @ lambda_prefix
        gauged_gamma_prefix = gauged_gamma_prefix @ gauged_forwards[index]
        gauged_lambda_prefix = gauged_reverses[index] @ gauged_lambda_prefix

    root = (
        rng.normal(size=(rank, 3)) + 1j * rng.normal(size=(rank, 3))
    ) / np.sqrt(2.0 * rank)
    root_energy = float(np.linalg.norm(root, "fro") ** 2)
    inverse_root_energy = float(
        np.linalg.norm(np.linalg.solve(gamma, root), "fro") ** 2
    )
    gauged_inverse_root_energy = float(
        np.linalg.norm(np.linalg.solve(gauged_gamma, root), "fro") ** 2
    )
    raw_energy = inverse_root_energy - root_energy
    gauged_raw_energy = gauged_inverse_root_energy - root_energy
    expected_gauged_energy = inverse_root_energy / gauge_product**2 - root_energy

    scalar_primes = [2, 3, 5, 7, 11, 13, 17, 19]
    scalar_rhos = [
        (1.0 - prime**-0.5) / (1.0 + prime**-0.5)
        for prime in scalar_primes
    ]
    scalar_rho = float(np.prod(scalar_rhos))
    scalar_gamma = scalar_rho * np.eye(rank, dtype=complex)
    scalar_lambda = np.eye(rank, dtype=complex)
    scalar_numerator = (
        scalar_gamma @ np.eye(rank) @ scalar_lambda
        - scalar_rho * np.eye(rank)
    )
    scalar_inverse_energy = (scalar_rho**-2 - 1.0) * root_energy

    return {
        "maximum gauged one-step pair error": maximum_step_pair_error,
        "gauged forward product error": relative_error(
            gauged_gamma,
            gauge_product * gamma,
        ),
        "gauged reverse product error": relative_error(
            gauged_lambda,
            lamb / gauge_product,
        ),
        "ordered response gauge error": relative_error(
            gauged_ordered,
            ordered,
        ),
        "relative numerator gauge error": relative_error(
            gauged_numerator,
            numerator,
        ),
        "maximum local numerator gauge error": maximum_local_invariance_error,
        "original telescope error": relative_error(telescope, numerator),
        "gauged telescope error": relative_error(gauged_telescope, numerator),
        "raw inverse energy law error": relative_error(
            gauged_raw_energy,
            expected_gauged_energy,
        ),
        "scalar channel numerator norm": float(
            np.linalg.norm(scalar_numerator, 2)
        ),
        "raw inverse energy": raw_energy,
        "gauged raw inverse energy": gauged_raw_energy,
        "scalar rho product": scalar_rho,
        "scalar inverse norm": scalar_rho**-1,
        "scalar raw inverse energy": scalar_inverse_energy,
        "gauge product": gauge_product,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=6)
    parser.add_argument("--seed", type=int, default=397)
    parser.add_argument("--tolerance", type=float, default=3e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 397 paired-Schur scalar-gauge audit certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum gauged one-step pair error",
        "gauged forward product error",
        "gauged reverse product error",
        "ordered response gauge error",
        "relative numerator gauge error",
        "maximum local numerator gauge error",
        "original telescope error",
        "gauged telescope error",
        "raw inverse energy law error",
        "scalar channel numerator norm",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"paired scalar-gauge audit failed: {maximum_error:.3e}")
    if abs(checks["gauged raw inverse energy"] - checks["raw inverse energy"]) <= 1e-3:
        raise RuntimeError("chosen scalar gauge did not change the raw energy")
    if checks["scalar inverse norm"] <= 100.0:
        raise RuntimeError("scalar guard did not expose large inverse growth")
    if checks["scalar raw inverse energy"] <= 1e4:
        raise RuntimeError("scalar raw inverse energy is accidentally small")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("ordered_response=GAUGE_INVARIANT")
    print("relative_numerator=GAUGE_INVARIANT")
    print("raw_inverse_energy=GAUGE_DEPENDENT")
    print("uniform_rho_relative_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
