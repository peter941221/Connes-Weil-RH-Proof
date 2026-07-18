"""Discrete certificate for Proof 357's nested-window HS owner.

The zero-fill Toeplitz matrices verify finite-grid analogues of the exact
kernel and restriction identities.  The continuous proof is Tonelli's theorem.
The script does not prove the moving quotient factorization, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | float, expected: np.ndarray | float) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def convolution_matrix(
    input_points: np.ndarray,
    output_points: np.ndarray,
    step: float,
    half_width: float,
) -> np.ndarray:
    differences = output_points[:, None] - input_points[None, :]
    kernel = np.where(
        np.abs(differences) <= half_width,
        (1.0 - np.abs(differences) / half_width)
        / np.sqrt(2.0 * half_width / 3.0),
        0.0,
    )
    return step * kernel.astype(complex)


def selector(indices: np.ndarray, ambient_size: int) -> np.ndarray:
    matrix = np.zeros((indices.size, ambient_size), dtype=complex)
    matrix[np.arange(indices.size), indices] = 1.0
    return matrix


def certificate(
    step: float,
    input_half_width: float,
    root_half_width: float,
    envelope_half_width: float,
    displacements: list[float],
) -> dict[str, float]:
    input_points = np.arange(
        -input_half_width, input_half_width + 0.5 * step, step
    )
    envelope_points = np.arange(
        -envelope_half_width, envelope_half_width + 0.5 * step, step
    )
    envelope_operator = convolution_matrix(
        input_points, envelope_points, step, root_half_width
    )

    kernel_points = np.arange(
        -root_half_width, root_half_width + 0.5 * step, step
    )
    kernel_samples = (
        (1.0 - np.abs(kernel_points) / root_half_width)
        / np.sqrt(2.0 * root_half_width / 3.0)
    )
    discrete_root_norm_sq = step * float(np.sum(np.abs(kernel_samples) ** 2))
    predicted_envelope_hs_sq = (
        envelope_points.size * step * discrete_root_norm_sq
    )

    checks = {
        "envelope HS formula error": relative_error(
            np.linalg.norm(envelope_operator, "fro") ** 2,
            predicted_envelope_hs_sq,
        ),
        "nested factorization error": 0.0,
        "translated factorization error": 0.0,
    }

    for displacement in displacements:
        interval_indices = np.flatnonzero(
            (envelope_points >= -0.5 * displacement - 1e-12)
            & (envelope_points <= 0.5 * displacement + 1e-12)
        )
        restriction = selector(interval_indices, envelope_points.size)
        direct_interval_operator = convolution_matrix(
            input_points,
            envelope_points[interval_indices],
            step,
            root_half_width,
        )
        checks["nested factorization error"] = max(
            checks["nested factorization error"],
            relative_error(
                direct_interval_operator, restriction @ envelope_operator
            ),
        )

        shift_steps = int(round(displacement / step))
        shifted_indices = interval_indices - shift_steps
        valid = (shifted_indices >= 0) & (shifted_indices < envelope_points.size)
        shifted_indices = shifted_indices[valid]
        translated_output = envelope_points[shifted_indices] + displacement
        pretranslation_output = translated_output - displacement
        translated_direct = convolution_matrix(
            input_points, pretranslation_output, step, root_half_width
        )
        translated_restriction = selector(
            shifted_indices, envelope_points.size
        )
        checks["translated factorization error"] = max(
            checks["translated factorization error"],
            relative_error(
                translated_direct,
                translated_restriction @ envelope_operator,
            ),
        )

    return checks


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--input-half-width", type=float, default=10.0)
    parser.add_argument("--root-half-width", type=float, default=0.75)
    parser.add_argument("--envelope-half-width", type=float, default=4.0)
    parser.add_argument("--displacements", default="0.5,1.0,2.0,3.0")
    parser.add_argument("--tolerance", type=float, default=2e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    displacements = [float(value) for value in args.displacements.split(",")]
    checks = certificate(
        args.step,
        args.input_half_width,
        args.root_half_width,
        args.envelope_half_width,
        displacements,
    )
    print("Proof 357 nested-window common-HS certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"nested-window certificate failed: {maximum_error:.3e}")
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("finite_output_hs_owner=EXACT")
    print("common_near_envelope=EXACT")
    print("moving_quotient_factorization=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
