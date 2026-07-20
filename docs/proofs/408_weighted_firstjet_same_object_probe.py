"""Finite same-object certificate for Proof 408.

The source frame is intentionally non-orthogonal after the fixed multiplier
D_g.  The weighted Gram determinant derivative and the direct orthogonal
projection response are compared before the transport first jet is taken.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def random_frame(ambient: int, rank: int, rng: np.random.Generator) -> np.ndarray:
    raw = rng.normal(size=(ambient, rank)) + 1j * rng.normal(size=(ambient, rank))
    frame, _ = np.linalg.qr(raw, mode="reduced")
    return frame


def projection(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.solve(gram, frame.conj().T)


def weighted_detector_trace(
    frame: np.ndarray, detector_values: np.ndarray
) -> complex:
    gram = frame.conj().T @ frame
    numerator = frame.conj().T @ (detector_values[:, None] * frame)
    return complex(np.trace(np.linalg.solve(gram, numerator)))


def certificate(
    ambient: int, rank: int, seed: int, transport_step: float
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    source = random_frame(ambient, rank, rng)

    carrier_values = 0.82 + 0.21 * np.cos(np.linspace(-1.7, 2.2, ambient))
    carrier = carrier_values.astype(complex)
    frame = carrier[:, None] * source

    detector_values = 0.3 + 0.17 * np.cos(np.linspace(-2.0, 2.4, ambient))
    detector_values += 0.07 * np.sin(np.linspace(-0.4, 3.1, ambient))
    detector = np.diag(detector_values.astype(complex))

    generator_values = 0.14 * np.sin(np.linspace(-2.2, 2.8, ambient)).astype(
        complex
    )
    generator_values += 0.08j * np.cos(np.linspace(-1.1, 2.0, ambient))
    generator = np.diag(generator_values)

    source_projection = projection(frame)
    identity = np.eye(ambient, dtype=complex)
    complement = identity - source_projection
    commutator = detector @ complement - complement @ detector
    predicted_first_jet = 2.0 * np.real(
        np.trace(
            source_projection
            @ commutator
            @ complement
            @ generator
            @ source_projection
        )
    )

    def response(parameter: float) -> complex:
        tau = 1.0 + parameter * generator_values
        moved_frame = tau[:, None] * frame
        return weighted_detector_trace(moved_frame, detector_values) - weighted_detector_trace(
            frame, detector_values
        )

    plus = response(transport_step)
    minus = response(-transport_step)
    finite_transport_derivative = (plus - minus) / (2.0 * transport_step)

    # The detector derivative of the weighted relative determinant is the same
    # Gram trace used by response().  Compute it independently from matrices.
    moved_tau = 1.0 + transport_step * generator_values
    moved_frame = moved_tau[:, None] * frame
    weighted_response = weighted_detector_trace(moved_frame, detector_values)
    direct_projection_response = np.trace(
        detector @ (projection(moved_frame) - source_projection)
    )

    raw_frame = source
    raw_source_response = weighted_detector_trace(raw_frame, detector_values)
    weighted_source_response = weighted_detector_trace(frame, detector_values)
    raw_response = weighted_detector_trace(
        moved_tau[:, None] * raw_frame, detector_values
    ) - raw_source_response

    return {
        "source_gram_condition": float(np.linalg.cond(frame.conj().T @ frame)),
        "weighted_projection_response_error": abs(
            (weighted_response - weighted_source_response)
            - direct_projection_response
        ),
        "weighted_transport_derivative_error": abs(
            finite_transport_derivative - predicted_first_jet
        ),
        "weighted_vs_raw_response_gap": abs(
            weighted_source_response - raw_source_response
        ),
        "transported_frame_rank": float(np.linalg.matrix_rank(moved_frame)),
        "weighted_response_magnitude": abs(plus),
        "first_jet_magnitude": abs(predicted_first_jet),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient", type=int, default=36)
    parser.add_argument("--rank", type=int, default=8)
    parser.add_argument("--seed", type=int, default=408)
    parser.add_argument("--transport-step", type=float, default=1e-5)
    parser.add_argument("--tolerance", type=float, default=3e-8)
    args = parser.parse_args()

    checks = certificate(args.ambient, args.rank, args.seed, args.transport_step)
    print("Proof 408 weighted first-jet same-object certificate")
    for label, value in checks.items():
        print(f"{label}={value:.12e}")

    exact_labels = [
        "weighted_projection_response_error",
        "weighted_transport_derivative_error",
    ]
    maximum_exact_error = max(checks[label] for label in exact_labels)
    if maximum_exact_error > args.tolerance:
        raise RuntimeError(f"weighted first jet failed: {maximum_exact_error:.3e}")
    if checks["weighted_vs_raw_response_gap"] <= 1e-5:
        raise RuntimeError("weighted and raw responses accidentally agree")
    if checks["transported_frame_rank"] < args.rank:
        raise RuntimeError("transported source frame lost rank")

    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    print("weighted_determinant_to_projection=EXACT_FINITE_MODEL")
    print("weighted_projection_to_proof405_first_jet=EXACT_FINITE_MODEL")
    print("physical_two_branch_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
