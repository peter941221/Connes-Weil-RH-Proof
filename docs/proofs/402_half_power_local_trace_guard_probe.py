"""Exact certificate for Proof 402's half-power local-trace guard."""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def certificate(coupling: float) -> dict[str, float]:
    identity = np.eye(2, dtype=float)
    unitary = np.array([[0.0, 1.0], [1.0, 0.0]])
    source_projection = np.diag([1.0, 0.0])
    detector = identity + coupling * unitary
    primes = [2, 3, 5, 7, 11, 23, 47, 97, 193, 389, 769, 1543, 3079]

    maximum_projection_error = 0.0
    maximum_response_error = 0.0
    maximum_covariance_violation = 0.0
    scaled_linear_values: list[float] = []
    scaled_quadratic_values: list[float] = []

    source = np.array([[1.0], [0.0]])
    for prime in primes:
        coefficient = prime**-0.5
        transport = identity - coefficient * unitary
        moved = np.linalg.inv(transport) @ source
        moved /= np.linalg.norm(moved)
        moved_projection = moved @ moved.T
        predicted_projection = np.array(
            [[1.0, coefficient], [coefficient, coefficient * coefficient]]
        ) / (1.0 + coefficient * coefficient)
        response = float(
            np.trace(detector @ (moved_projection - source_projection))
        )
        predicted_response = (
            2.0 * coupling * coefficient / (1.0 + coefficient * coefficient)
        )

        rho = (1.0 - coefficient) / (1.0 + coefficient)
        markov = (1.0 - coefficient) * np.linalg.inv(transport)
        covariance = float((source.T @ markov.T @ markov @ source)[0, 0])
        maximum_covariance_violation = max(
            maximum_covariance_violation,
            max(0.0, rho * rho - covariance),
            max(0.0, covariance - 1.0),
        )
        maximum_projection_error = max(
            maximum_projection_error,
            relative_error(moved_projection, predicted_projection),
        )
        maximum_response_error = max(
            maximum_response_error,
            relative_error(response, predicted_response),
        )
        scaled_linear_values.append(response / coefficient)
        scaled_quadratic_values.append(abs(response) / (coefficient**2))

    detector_eigenvalues = np.linalg.eigvalsh(detector)
    return {
        "unitary violation": relative_error(unitary.T @ unitary, identity),
        "detector commutator error": relative_error(
            detector @ unitary, unitary @ detector
        ),
        "detector positivity violation": max(
            0.0, -float(detector_eigenvalues.min())
        ),
        "maximum projection formula error": maximum_projection_error,
        "maximum response formula error": maximum_response_error,
        "maximum covariance violation": maximum_covariance_violation,
        "terminal linear scaling error": abs(
            scaled_linear_values[-1] - 2.0 * coupling
        ),
        "initial quadratic ratio": scaled_quadratic_values[0],
        "terminal quadratic ratio": scaled_quadratic_values[-1],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coupling", type=float, default=0.6)
    parser.add_argument("--tolerance", type=float, default=3e-8)
    args = parser.parse_args()
    if not 0.0 < args.coupling < 1.0:
        raise ValueError("coupling must lie in (0,1)")

    checks = certificate(args.coupling)
    print("Proof 402 half-power local-trace guard certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "unitary violation",
        "detector commutator error",
        "detector positivity violation",
        "maximum projection formula error",
        "maximum response formula error",
        "maximum covariance violation",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"half-power guard failed: {maximum_error:.3e}")
    if checks["terminal linear scaling error"] > 5e-4:
        raise RuntimeError("response does not retain its linear coefficient")
    if checks["terminal quadratic ratio"] <= 20.0 * checks["initial quadratic ratio"]:
        raise RuntimeError("quadratic normalization does not expose divergence")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("positive_commuting_guard=EXACT")
    print("generic_prime_square_gain=REJECTED")
    print("source_first_variation_cancellation=REQUIRED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
