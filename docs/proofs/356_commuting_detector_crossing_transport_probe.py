"""Certificate for Proof 356's commuting-detector crossing transport.

The random matrices verify the exact Gram-frame identity.  The two-dimensional
cohort verifies sharp condition-number amplification.  Neither proves the
complete sequential observation-row bound, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def random_isometry(
    ambient_size: int, rank: int, rng: np.random.Generator
) -> np.ndarray:
    matrix = rng.normal(size=(ambient_size, rank)) + 1j * rng.normal(
        size=(ambient_size, rank)
    )
    isometry, _ = np.linalg.qr(matrix)
    return isometry[:, :rank]


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 0.0:
        raise RuntimeError("matrix is not positive definite")
    return eigenvectors @ np.diag(eigenvalues ** -0.5) @ eigenvectors.conj().T


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def random_crossing_check(
    ambient_size: int, rank: int, prime: int, seed: int
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    frequencies = rng.uniform(-3.0, 3.0, size=ambient_size)
    detector = np.diag(
        (
            0.7
            + 0.2 * np.cos(frequencies)
            + 0.1 * np.sin(1.7 * frequencies)
        ).astype(complex)
    )
    translation = np.diag(
        np.exp(1j * math.log(prime) * frequencies)
    )
    coefficient = prime ** -0.5
    transport = np.linalg.inv(
        np.eye(ambient_size, dtype=complex) - coefficient * translation
    )

    source_isometry = random_isometry(ambient_size, rank, rng)
    source_projection = source_isometry @ source_isometry.conj().T
    gram = source_isometry.conj().T @ transport.conj().T @ transport @ source_isometry
    target_isometry = transport @ source_isometry @ inverse_positive_square_root(gram)
    target_projection = target_isometry @ target_isometry.conj().T

    source_crossing = (
        (np.eye(ambient_size, dtype=complex) - source_projection)
        @ detector
        @ source_isometry
    )
    target_crossing = (
        (np.eye(ambient_size, dtype=complex) - target_projection)
        @ detector
        @ target_isometry
    )
    transported_crossing = (
        (np.eye(ambient_size, dtype=complex) - target_projection)
        @ transport
        @ (np.eye(ambient_size, dtype=complex) - source_projection)
        @ source_crossing
        @ inverse_positive_square_root(gram)
    )

    scale = 2.3 - 0.7j
    scaled_transport = scale * transport
    scaled_gram = (
        source_isometry.conj().T
        @ scaled_transport.conj().T
        @ scaled_transport
        @ source_isometry
    )
    scaled_target_frame = (
        scaled_transport
        @ source_isometry
        @ inverse_positive_square_root(scaled_gram)
    )
    scaled_target_projection = scaled_target_frame @ scaled_target_frame.conj().T

    return {
        "transport detector commutator error": relative_error(
            transport @ detector, detector @ transport
        ),
        "target isometry error": relative_error(
            target_isometry.conj().T @ target_isometry,
            np.eye(rank, dtype=complex),
        ),
        "crossing transport error": relative_error(
            target_crossing, transported_crossing
        ),
        "scale-invariant projection error": relative_error(
            scaled_target_projection, target_projection
        ),
    }


def sharp_guard(prime: int, angles: list[float]) -> tuple[float, float]:
    coefficient = prime ** -0.5
    condition_number = (1.0 + coefficient) / (1.0 - coefficient)
    maximum_formula_error = 0.0
    final_ratio_error = 0.0
    for angle in angles:
        tangent = math.tan(angle)
        new_angle = math.atan(condition_number * tangent)
        old_crossing = abs(math.sin(angle) * math.cos(angle))
        new_crossing = abs(math.sin(new_angle) * math.cos(new_angle))
        measured_ratio = new_crossing / old_crossing
        exact_ratio = (
            condition_number
            * (1.0 + tangent * tangent)
            / (1.0 + condition_number * condition_number * tangent * tangent)
        )
        maximum_formula_error = max(
            maximum_formula_error, abs(measured_ratio - exact_ratio)
        )
        final_ratio_error = abs(measured_ratio - condition_number)
    return maximum_formula_error, final_ratio_error


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=44)
    parser.add_argument("--rank", type=int, default=18)
    parser.add_argument("--seed", type=int, default=356)
    parser.add_argument("--tolerance", type=float, default=5e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks: dict[str, float] = {}
    for prime in [2, 3, 5, 11, 101]:
        random_checks = random_crossing_check(
            args.ambient_size, args.rank, prime, args.seed + prime
        )
        for label, value in random_checks.items():
            checks[label] = max(checks.get(label, 0.0), value)

    angles = [1e-2, 1e-3, 1e-4, 1e-5, 1e-6]
    guard_limit_errors = []
    for prime in [2, 3, 5, 11, 101]:
        formula_error, limit_error = sharp_guard(prime, angles)
        checks["sharp guard formula error"] = max(
            checks.get("sharp guard formula error", 0.0), formula_error
        )
        guard_limit_errors.append((prime, limit_error))

    print("Proof 356 commuting-detector crossing certificate")
    for label, value in checks.items():
        print(f"maximum_{label.replace(' ', '_')}={value:.12e}")
    for prime, value in guard_limit_errors:
        print(f"p={prime}_small_angle_condition_number_error={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"crossing transport certificate failed: {maximum_error:.3e}")
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("commuting_crossing_transport=EXACT")
    print("condition_number_amplification=SHARP")
    print("complete_observation_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
