#!/usr/bin/env python3
"""Finite certificate for the transported Burnol boundary-Gram owner.

The certificate verifies the complement-frame formula, the boundary trace
readback, and the relative Gram log-determinant derivative.  It checks exact
linear algebra only and does not prove the uniform Gate 3U estimate.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    q, r = np.linalg.qr(matrix)
    phases = np.diag(r)
    phases = phases / np.maximum(np.abs(phases), 1e-15)
    return q @ np.diag(np.conj(phases))


def orthonormal_frame(
    ambient_dimension: int, frame_dimension: int, rng: np.random.Generator
) -> np.ndarray:
    matrix = rng.normal(size=(ambient_dimension, frame_dimension)) + 1j * rng.normal(
        size=(ambient_dimension, frame_dimension)
    )
    frame, _ = np.linalg.qr(matrix)
    return frame[:, :frame_dimension]


def projection_from_frame(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.inv(gram) @ frame.conj().T


def certificate(size: int, complement_dimension: int, seed: int) -> dict[str, float]:
    if complement_dimension <= 0 or complement_dimension >= size:
        raise ValueError("complement dimension must lie strictly between 0 and size")
    rng = np.random.default_rng(seed)
    complement_frame = orthonormal_frame(size, complement_dimension, rng)
    complement = complement_frame @ complement_frame.conj().T
    sonin = np.eye(size, dtype=complex) - complement

    spectral_basis = random_unitary(size, rng)
    transport_values = np.exp(
        rng.uniform(-0.65, 0.55, size=size)
        + 1j * rng.uniform(-0.8, 0.8, size=size)
    )
    detector_values = rng.uniform(-0.9, 1.2, size=size)
    transport = spectral_basis @ np.diag(transport_values) @ spectral_basis.conj().T
    detector = spectral_basis @ np.diag(detector_values) @ spectral_basis.conj().T
    transport_inverse = np.linalg.inv(transport)

    transported_sonin_frame = transport @ orthonormal_frame(
        size, size - complement_dimension, rng
    )
    # Replace the random Sonin frame by an exact frame for Ran(sonin).
    sonin_values, sonin_vectors = np.linalg.eigh(sonin)
    sonin_frame = sonin_vectors[:, sonin_values > 0.5]
    transported_sonin_frame = transport @ sonin_frame
    transported_sonin = projection_from_frame(transported_sonin_frame)
    transported_complement_direct = np.eye(size, dtype=complex) - transported_sonin

    inverse_metric = transport_inverse @ transport_inverse.conj().T
    source_gram = complement_frame.conj().T @ complement_frame
    transported_gram = (
        complement_frame.conj().T @ inverse_metric @ complement_frame
    )
    transported_complement_frame = transport_inverse.conj().T @ complement_frame
    transported_complement_formula = (
        transported_complement_frame
        @ np.linalg.inv(transported_gram)
        @ transported_complement_frame.conj().T
    )

    response_direct = np.trace(
        detector @ (transported_complement_direct - complement)
    )
    numerator_transported = (
        complement_frame.conj().T
        @ detector
        @ inverse_metric
        @ complement_frame
    )
    numerator_source = complement_frame.conj().T @ detector @ complement_frame
    response_boundary = np.trace(
        np.linalg.inv(transported_gram) @ numerator_transported
        - np.linalg.inv(source_gram) @ numerator_source
    )

    def relative_log_determinant(parameter: float) -> complex:
        exponential = (
            spectral_basis
            @ np.diag(np.exp(parameter * detector_values))
            @ spectral_basis.conj().T
        )
        moving = complement_frame.conj().T @ exponential @ inverse_metric @ complement_frame
        base = complement_frame.conj().T @ exponential @ complement_frame
        sign_m, logabs_m = np.linalg.slogdet(moving)
        sign_b, logabs_b = np.linalg.slogdet(base)
        return (
            np.log(sign_m) + logabs_m
            - np.log(sign_b) - logabs_b
            - (np.linalg.slogdet(transported_gram)[1] - np.linalg.slogdet(source_gram)[1])
        )

    step = 2e-6
    derivative = (
        relative_log_determinant(step) - relative_log_determinant(-step)
    ) / (2.0 * step)

    return {
        "transport detector commutator error": relative_error(
            transport @ detector, detector @ transport
        ),
        "transported complement formula error": relative_error(
            transported_complement_formula, transported_complement_direct
        ),
        "transported complement idempotence error": relative_error(
            transported_complement_formula @ transported_complement_formula,
            transported_complement_formula,
        ),
        "boundary response error": relative_error(response_boundary, response_direct),
        "relative determinant derivative error": relative_error(
            derivative, response_direct
        ),
        "response magnitude": float(abs(response_direct)),
        "transported Gram condition number": float(np.linalg.cond(transported_gram)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=18)
    parser.add_argument("--complement-dimension", type=int, default=8)
    parser.add_argument("--seed", type=int, default=341)
    parser.add_argument("--tolerance", type=float, default=2e-8)
    args = parser.parse_args()
    checks = certificate(args.size, args.complement_dimension, args.seed)
    print("identity=transported Burnol boundary Gram response")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    exact_error = max(
        checks["transport detector commutator error"],
        checks["transported complement formula error"],
        checks["transported complement idempotence error"],
        checks["boundary response error"],
        checks["relative determinant derivative error"],
    )
    if exact_error > args.tolerance:
        raise RuntimeError(f"boundary Gram certificate failed: {exact_error:.3e}")
    if checks["response magnitude"] <= 1e-7:
        raise RuntimeError("certificate response unexpectedly vanished")
    print(f"maximum_exact_error={exact_error:.12e}")
    print("complete_boundary_projection_owner=EXACT")
    print("relative_gram_determinant_first_jet=EXACT")
    print("uniform_markov_boundary_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
