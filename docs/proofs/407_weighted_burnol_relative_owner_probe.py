"""Finite certificate for Proof 407's weighted Burnol owner.

The model is intentionally one-dimensional.  K_Theta=span{1} is the model
space for Theta(z)=z, while g is an isometric multiplier on that space.  The
probe verifies that source compression transports to A_{a |g|^2}, and that
the tempting unweighted replacement A_a is false for a detector.
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


def boundary_nodes(size: int) -> np.ndarray:
    return np.exp(2j * np.pi * np.arange(size) / size)


def compressed_scalar(values: np.ndarray) -> complex:
    return complex(np.mean(values))


def rank_one_projection_trace(
    detector_values: np.ndarray, vector: np.ndarray
) -> complex:
    """Trace of a diagonal detector against a rank-one projection."""
    denominator = np.vdot(vector, vector)
    return complex(np.vdot(vector, detector_values * vector) / denominator)


def certificate(size: int, r: float, transport: float) -> dict[str, float]:
    nodes = boundary_nodes(size)

    g = (1.0 + r * nodes) / np.sqrt(1.0 + r * r)
    h = np.abs(g) ** 2
    detector_values = nodes + np.conjugate(nodes)

    # A_Theta(phi) for K_Theta=span{1} is the boundary average of phi.
    source_form = compressed_scalar(h)
    raw_detector_form = compressed_scalar(detector_values)
    weighted_detector_form = compressed_scalar(detector_values * h)

    source_vector = np.ones(size, dtype=complex)
    source_response = rank_one_projection_trace(detector_values, source_vector)
    weighted_response = rank_one_projection_trace(detector_values, g)

    tau = 1.0 - transport * nodes
    moved = tau * g
    moved_h = np.abs(moved) ** 2
    moved_response = rank_one_projection_trace(detector_values, moved)

    # Relative weighted Gram formula for the one-dimensional source.
    weighted_relative_response = (
        compressed_scalar(detector_values * moved_h)
        / compressed_scalar(moved_h)
        - weighted_detector_form / source_form
    )

    def relative_log_det(parameter: float) -> float:
        detector_weight = np.exp(parameter * detector_values.real)
        moved_term = compressed_scalar(moved_h * detector_weight)
        moved_base = compressed_scalar(moved_h)
        source_term = compressed_scalar(h * detector_weight)
        source_base = compressed_scalar(h)
        return float(
            np.log(moved_term / moved_base).real
            - np.log(source_term / source_base).real
        )

    derivative_step = 1e-6
    relative_det_derivative = (
        relative_log_det(derivative_step)
        - relative_log_det(-derivative_step)
    ) / (2.0 * derivative_step)

    # The tempting raw model formula drops h from both terms.
    raw_relative_response = (
        compressed_scalar(detector_values * np.abs(tau) ** 2)
        / compressed_scalar(np.abs(tau) ** 2)
        - raw_detector_form
    )

    return {
        "source_isometry_error": abs(source_form - 1.0),
        "source_projection_form_error": abs(source_response - raw_detector_form),
        "weighted_detector_form_error": abs(
            weighted_response - weighted_detector_form
        ),
        "weighted_relative_projection_error": abs(
            (moved_response - weighted_response) - weighted_relative_response
        ),
        "relative_log_det_derivative_error": abs(
            relative_det_derivative - weighted_relative_response.real
        ),
        "raw_unweighted_intertwining_gap": abs(
            weighted_detector_form - raw_detector_form
        ),
        "raw_vs_weighted_relative_gap": abs(
            weighted_relative_response - raw_relative_response
        ),
        "weighted_response_magnitude": abs(weighted_response),
        "relative_response_magnitude": abs(moved_response - weighted_response),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=4096)
    parser.add_argument("--r", type=float, default=0.37)
    parser.add_argument("--transport", type=float, default=0.29)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    args = parser.parse_args()

    checks = certificate(args.size, args.r, args.transport)
    print("Proof 407 weighted Burnol relative-owner certificate")
    for label, value in checks.items():
        print(f"{label}={value:.12e}")

    algebra_labels = [
        "source_isometry_error",
        "source_projection_form_error",
        "weighted_detector_form_error",
        "weighted_relative_projection_error",
    ]
    maximum_algebra_error = max(checks[label] for label in algebra_labels)
    maximum_certificate_error = max(
        maximum_algebra_error, checks["relative_log_det_derivative_error"]
    )
    if maximum_certificate_error > args.tolerance:
        raise RuntimeError(
            f"weighted projection owner failed: {maximum_certificate_error:.3e}"
        )
    if checks["raw_unweighted_intertwining_gap"] <= 1e-4:
        raise RuntimeError("raw unweighted gap was accidentally trivial")
    if checks["raw_vs_weighted_relative_gap"] <= 1e-4:
        raise RuntimeError("relative raw/weighted gap was accidentally trivial")

    print(f"maximum_algebra_error={maximum_algebra_error:.12e}")
    print(
        "relative_log_det_derivative_error="
        f"{checks['relative_log_det_derivative_error']:.12e}"
    )
    print(f"maximum_certificate_error={maximum_certificate_error:.12e}")
    print("weighted_compression_owner=EXACT_FINITE_MODEL")
    print("raw_unweighted_intertwining=REJECTED_AS_INFERENCE")
    print("continuous_root_relative_gradient=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
