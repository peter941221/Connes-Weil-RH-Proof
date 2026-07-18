#!/usr/bin/env python3
"""Finite algebra certificate for Proof 342's fixed-boundary Schur collapse.

This checks only exact finite-dimensional frame identities.  It does not
estimate the continuous quotient Gram and is not a proof of Gate 3U.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def projection_from_frame(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.inv(gram) @ frame.conj().T


def inverse_square_root(positive: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(positive)
    if float(np.min(eigenvalues)) <= 0.0:
        raise ValueError("matrix must be positive definite")
    return (
        eigenvectors
        @ np.diag(eigenvalues ** -0.5)
        @ eigenvectors.conj().T
    )


def certificate(size: int, window_dimension: int, strength: float, seed: int) -> dict[str, float]:
    if 2 * window_dimension >= size:
        raise ValueError("need 2 * window_dimension < size")

    dtype = complex
    identity = np.eye(size, dtype=dtype)
    reflection = np.fliplr(identity)

    # The right zero-fill shift preserves the final coordinate window, and
    # reflection exchanges it with its adjoint.
    shift = np.zeros((size, size), dtype=dtype)
    for column in range(size - 1):
        shift[column + 1, column] = 1.0

    window = np.arange(size - window_dimension, size)
    inclusion = identity[:, window]
    source_projection = inclusion @ inclusion.conj().T
    reflected_inclusion = reflection @ inclusion
    reflected_projection = reflected_inclusion @ reflected_inclusion.conj().T

    transport_inverse = np.linalg.inv(identity - strength * shift)
    transport_inverse_adjoint = transport_inverse.conj().T
    restricted_transport = inclusion.conj().T @ transport_inverse @ inclusion

    source_frame = np.column_stack((inclusion, reflected_inclusion))
    transported_frame = transport_inverse_adjoint @ source_frame
    reparameterized_frame = np.column_stack(
        (transport_inverse_adjoint @ inclusion, reflected_inclusion)
    )

    direct_projection = projection_from_frame(transported_frame)
    reparameterized_projection = projection_from_frame(reparameterized_frame)

    quotient_frame = (
        identity - reflected_projection
    ) @ transport_inverse_adjoint @ inclusion
    quotient_gram = quotient_frame.conj().T @ quotient_frame
    reduced_projection = reflected_projection + (
        quotient_frame
        @ np.linalg.inv(quotient_gram)
        @ quotient_frame.conj().T
    )

    source_quotient_frame = (identity - reflected_projection) @ inclusion
    source_quotient_gram = source_quotient_frame.conj().T @ source_quotient_frame
    source_projection_from_frame = projection_from_frame(source_frame)
    source_reduced_projection = reflected_projection + (
        source_quotient_frame
        @ np.linalg.inv(source_quotient_gram)
        @ source_quotient_frame.conj().T
    )

    rng = np.random.default_rng(seed)
    detector_seed = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    detector = detector_seed + detector_seed.conj().T
    direct_response = np.trace(
        detector @ (direct_projection - source_projection_from_frame)
    )
    reduced_response = np.trace(
        np.linalg.inv(quotient_gram)
        @ quotient_frame.conj().T
        @ detector
        @ quotient_frame
        - np.linalg.inv(source_quotient_gram)
        @ source_quotient_frame.conj().T
        @ detector
        @ source_quotient_frame
    )

    # Deliberately worsen the fixed source frame coordinates.  Polar
    # normalization must remove this condition number from the relative
    # response without changing either subspace.
    coordinate_basis, _ = np.linalg.qr(
        rng.normal(size=(window_dimension, window_dimension))
        + 1j * rng.normal(size=(window_dimension, window_dimension))
    )
    coordinate = coordinate_basis @ np.diag(
        np.geomspace(1.0, 1.0e2, window_dimension)
    )
    conditioned_source_frame = source_quotient_frame @ coordinate
    conditioned_source_gram = (
        conditioned_source_frame.conj().T @ conditioned_source_frame
    )
    polar_frame = conditioned_source_frame @ inverse_square_root(
        conditioned_source_gram
    )

    source_range_projection = projection_from_frame(source_quotient_frame)
    quotient_transport = (
        quotient_frame @ source_quotient_frame.conj().T
        + identity
        - source_range_projection
    )
    compressed_metric = (
        polar_frame.conj().T
        @ quotient_transport.conj().T
        @ quotient_transport
        @ polar_frame
    )
    compressed_numerator = (
        polar_frame.conj().T
        @ quotient_transport.conj().T
        @ detector
        @ quotient_transport
        @ polar_frame
    )
    polar_response = np.trace(
        np.linalg.solve(compressed_metric, compressed_numerator)
        - polar_frame.conj().T @ detector @ polar_frame
    )

    reflected_column = transport_inverse_adjoint @ reflected_inclusion
    expected_reflected_column = reflected_inclusion @ restricted_transport

    return {
        "reflection involution error": relative_error(reflection @ reflection, identity),
        "causal reflection error": relative_error(
            reflection @ transport_inverse @ reflection,
            transport_inverse_adjoint,
        ),
        "source invariance error": relative_error(
            transport_inverse @ inclusion,
            inclusion @ restricted_transport,
        ),
        "fixed reflected column error": relative_error(
            reflected_column, expected_reflected_column
        ),
        "frame reparameterization projection error": relative_error(
            direct_projection, reparameterized_projection
        ),
        "transported Schur projection error": relative_error(
            direct_projection, reduced_projection
        ),
        "source Schur projection error": relative_error(
            source_projection_from_frame, source_reduced_projection
        ),
        "endpoint response error": relative_error(direct_response, reduced_response),
        "polar-normalized response error": relative_error(
            direct_response, polar_response
        ),
        "response magnitude": float(abs(direct_response)),
        "quotient Gram condition number": float(np.linalg.cond(quotient_gram)),
        "conditioned source Gram condition number": float(
            np.linalg.cond(conditioned_source_gram)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=18)
    parser.add_argument("--window-dimension", type=int, default=6)
    parser.add_argument("--strength", type=float, default=0.43)
    parser.add_argument("--seed", type=int, default=342)
    parser.add_argument("--tolerance", type=float, default=2e-12)
    args = parser.parse_args()

    checks = certificate(
        args.size, args.window_dimension, args.strength, args.seed
    )
    print("identity=fixed Burnol boundary Schur collapse")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [label for label in checks if label.endswith("error")]
    exact_error = max(checks[label] for label in exact_labels)
    if exact_error > args.tolerance:
        raise RuntimeError(f"Schur-collapse certificate failed: {exact_error:.3e}")
    if checks["response magnitude"] <= 1e-8:
        raise RuntimeError("certificate response unexpectedly vanished")

    print(f"maximum_exact_error={exact_error:.12e}")
    print("fixed_reflected_boundary=EXACT")
    print("single_quotient_gram_owner=EXACT")
    print("fixed_source_gram_polar_cancellation=EXACT")
    print("uniform_quotient_signed_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
