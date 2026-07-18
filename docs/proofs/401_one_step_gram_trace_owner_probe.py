"""Finite certificate for Proof 401's one-step Gram trace owner."""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    raw = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    unitary, triangular = np.linalg.qr(raw)
    diagonal = np.diag(triangular)
    phases = diagonal / np.maximum(np.abs(diagonal), 1e-15)
    return unitary @ np.diag(np.conj(phases))


def certificate(size: int, rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    spectral_basis = random_unitary(size, rng)
    frequencies = np.linspace(-1.8, 2.2, size)

    def translation(time: float) -> np.ndarray:
        return (
            spectral_basis
            @ np.diag(np.exp(1j * time * frequencies))
            @ spectral_basis.conj().T
        )

    detector = (
        spectral_basis
        @ np.diag(0.4 + rng.random(size))
        @ spectral_basis.conj().T
    )
    old_frame = random_unitary(size, rng)[:, :rank]
    initial_projection = old_frame @ old_frame.conj().T
    gamma = np.eye(rank, dtype=complex)

    maximum_intertwining_error = 0.0
    maximum_pair_error = 0.0
    maximum_trace_error = 0.0
    maximum_covariance_violation = 0.0
    maximum_local_inverse = 0.0
    physical_sum = 0.0 + 0.0j
    local_trace_sum = 0.0 + 0.0j

    for prime in [2, 3, 5, 7, 11, 13, 17, 19, 23]:
        coefficient = prime**-0.5
        rho = (1.0 - coefficient) / (1.0 + coefficient)
        unitary = translation(np.log(prime))
        transport = np.eye(size, dtype=complex) - coefficient * unitary
        normalized_forward = transport / (1.0 + coefficient)
        markov_inverse = (1.0 - coefficient) * np.linalg.inv(transport)

        moved_raw = markov_inverse @ old_frame
        new_frame, reverse = np.linalg.qr(moved_raw)
        diagonal = np.diag(reverse)
        phases = diagonal / np.maximum(np.abs(diagonal), 1e-15)
        new_frame = new_frame @ np.diag(phases)
        reverse = np.diag(np.conj(phases)) @ reverse
        forward = old_frame.conj().T @ normalized_forward @ new_frame

        old_alpha = old_frame.conj().T @ detector @ old_frame
        new_alpha = new_frame.conj().T @ detector @ new_frame
        local = forward @ new_alpha @ reverse - rho * old_alpha
        old_projection = old_frame @ old_frame.conj().T
        new_projection = new_frame @ new_frame.conj().T
        physical_increment = np.trace(
            detector @ (new_projection - old_projection)
        )

        covariance = reverse.conj().T @ reverse
        covariance_eigenvalues = np.linalg.eigvalsh(covariance)
        maximum_covariance_violation = max(
            maximum_covariance_violation,
            max(0.0, rho * rho - float(covariance_eigenvalues.min())),
            max(0.0, float(covariance_eigenvalues.max()) - 1.0),
        )
        maximum_local_inverse = max(
            maximum_local_inverse,
            float(np.linalg.norm(np.linalg.inv(covariance), 2)),
        )
        maximum_intertwining_error = max(
            maximum_intertwining_error,
            relative_error(
                normalized_forward @ new_frame,
                old_frame @ forward,
            ),
            relative_error(markov_inverse @ old_frame, new_frame @ reverse),
        )
        maximum_pair_error = max(
            maximum_pair_error,
            relative_error(
                forward @ reverse,
                rho * np.eye(rank, dtype=complex),
            ),
        )
        maximum_trace_error = max(
            maximum_trace_error,
            relative_error(np.trace(local) / rho, physical_increment),
        )

        gamma = gamma @ forward
        physical_sum += physical_increment
        local_trace_sum += np.trace(local) / rho
        old_frame = new_frame

    endpoint_projection = old_frame @ old_frame.conj().T
    return {
        "maximum intertwining error": maximum_intertwining_error,
        "maximum scalar pair error": maximum_pair_error,
        "maximum local trace readback error": maximum_trace_error,
        "signed local sum error": relative_error(local_trace_sum, physical_sum),
        "endpoint projection telescope error": relative_error(
            physical_sum,
            np.trace(
                detector
                @ (
                    endpoint_projection
                    - initial_projection
                )
            ),
        ),
        "maximum covariance violation": maximum_covariance_violation,
        "maximum local covariance inverse": maximum_local_inverse,
        "complete forward inverse norm": float(np.linalg.norm(np.linalg.inv(gamma), 2)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=22)
    parser.add_argument("--rank", type=int, default=8)
    parser.add_argument("--seed", type=int, default=401)
    parser.add_argument("--tolerance", type=float, default=4e-9)
    args = parser.parse_args()

    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 401 one-step Gram trace owner certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum intertwining error",
        "maximum scalar pair error",
        "maximum local trace readback error",
        "signed local sum error",
        "endpoint projection telescope error",
        "maximum covariance violation",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"one-step Gram owner failed: {maximum_error:.3e}")
    if checks["maximum local covariance inverse"] >= 34.0:
        raise RuntimeError("one-step covariance exceeded the absolute bound")
    if checks["complete forward inverse norm"] <= 10.0:
        raise RuntimeError("complete cascade does not expose cumulative conditioning")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("local_projection_increment=EXACT")
    print("one_step_inverse_bound=UNIFORM")
    print("signed_increment_sum_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
