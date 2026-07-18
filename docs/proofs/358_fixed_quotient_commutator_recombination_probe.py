"""Finite certificate for Proof 358's quotient commutator recombination.

The matrices check exact commutator and Gram-normalized transport identities.
They do not prove the complete observation-row estimate, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse

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


def certificate(
    ambient_size: int,
    quotient_rank: int,
    boundary_rank: int,
    seed: int,
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    total_fixed_rank = quotient_rank + boundary_rank
    fixed_frame = random_isometry(ambient_size, total_fixed_rank, rng)
    quotient_isometry = fixed_frame[:, :quotient_rank]
    boundary_isometry = fixed_frame[:, quotient_rank:]
    quotient_projection = quotient_isometry @ quotient_isometry.conj().T
    boundary_projection = boundary_isometry @ boundary_isometry.conj().T
    sonin_projection = (
        np.eye(ambient_size, dtype=complex)
        - boundary_projection
        - quotient_projection
    )

    support_frame = random_isometry(ambient_size, ambient_size // 2, rng)
    fourier_frame = random_isometry(ambient_size, ambient_size // 2, rng)
    support_projection = support_frame @ support_frame.conj().T
    fourier_projection = fourier_frame @ fourier_frame.conj().T
    prolate_correction = (
        support_projection @ fourier_projection @ support_projection
        - sonin_projection
    )

    frequencies = rng.uniform(-2.5, 2.5, size=ambient_size)
    detector = np.diag(
        (0.6 + 0.3 * np.cos(frequencies) + 0.1 * np.sin(1.4 * frequencies)).astype(
            complex
        )
    )
    identity = np.eye(ambient_size, dtype=complex)

    def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
        return left @ right - right @ left

    direct_quotient_commutator = commutator(detector, quotient_projection)
    physical_bracket = (
        -commutator(detector, boundary_projection)
        -commutator(detector, support_projection)
        @ fourier_projection
        @ support_projection
        -support_projection
        @ commutator(detector, fourier_projection)
        @ support_projection
        -support_projection
        @ fourier_projection
        @ commutator(detector, support_projection)
        +commutator(detector, prolate_correction)
    )
    direct_crossing = (
        (identity - quotient_projection)
        @ detector
        @ quotient_isometry
    )
    bracket_crossing = physical_bracket @ quotient_isometry

    phases = rng.uniform(-np.pi, np.pi, size=ambient_size)
    magnitudes = rng.uniform(0.4, 1.7, size=ambient_size)
    transport = np.diag(magnitudes * np.exp(1j * phases))
    gram = (
        quotient_isometry.conj().T
        @ transport.conj().T
        @ transport
        @ quotient_isometry
    )
    transported_isometry = (
        transport @ quotient_isometry @ inverse_positive_square_root(gram)
    )
    transported_projection = transported_isometry @ transported_isometry.conj().T
    transported_crossing = (
        (identity - transported_projection)
        @ detector
        @ transported_isometry
    )
    pulled_crossing = (
        (identity - transported_projection)
        @ transport
        @ (identity - quotient_projection)
        @ physical_bracket
        @ quotient_isometry
        @ inverse_positive_square_root(gram)
    )

    scale = -1.1 + 2.0j
    scaled_transport = scale * transport
    scaled_gram = (
        quotient_isometry.conj().T
        @ scaled_transport.conj().T
        @ scaled_transport
        @ quotient_isometry
    )
    scaled_frame = (
        scaled_transport
        @ quotient_isometry
        @ inverse_positive_square_root(scaled_gram)
    )

    return {
        "quotient decomposition error": relative_error(
            quotient_projection, identity - sonin_projection - boundary_projection
        ),
        "physical commutator error": relative_error(
            direct_quotient_commutator, physical_bracket
        ),
        "fixed crossing error": relative_error(direct_crossing, bracket_crossing),
        "transport detector commutator error": relative_error(
            transport @ detector, detector @ transport
        ),
        "transported crossing error": relative_error(
            transported_crossing, pulled_crossing
        ),
        "scaled projection error": relative_error(
            scaled_frame @ scaled_frame.conj().T, transported_projection
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=42)
    parser.add_argument("--quotient-rank", type=int, default=13)
    parser.add_argument("--boundary-rank", type=int, default=11)
    parser.add_argument("--seed", type=int, default=358)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.ambient_size,
        args.quotient_rank,
        args.boundary_rank,
        args.seed,
    )
    print("Proof 358 fixed-quotient commutator certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"quotient commutator certificate failed: {maximum_error:.3e}")
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("fixed_physical_commutator=EXACT")
    print("moving_prefix_crossing=EXACT")
    print("complete_observation_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
