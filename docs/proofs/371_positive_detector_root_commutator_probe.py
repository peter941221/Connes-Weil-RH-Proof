"""Finite certificate for Proof 371's positive-detector root reduction.

The script verifies the exact block factorization and Frobenius bounds.  It
does not prove the moving root-commutator row, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def relative_error(actual: np.ndarray | float, expected: np.ndarray | float) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def random_isometry(
    ambient_size: int,
    source_size: int,
    rng: np.random.Generator,
) -> np.ndarray:
    matrix = rng.normal(size=(ambient_size, source_size)) + 1j * rng.normal(
        size=(ambient_size, source_size)
    )
    isometry, _ = np.linalg.qr(matrix)
    return isometry[:, :source_size]


def certificate(ambient_size: int, source_size: int, seed: int) -> dict[str, float]:
    if not 1 < source_size < ambient_size:
        raise ValueError("require 1 < source size < ambient size")
    rng = np.random.default_rng(seed)
    frame = random_isometry(ambient_size, source_size, rng)
    projection = frame @ frame.conj().T
    complement = np.eye(ambient_size, dtype=complex) - projection
    root = rng.normal(size=(ambient_size, ambient_size)) + 1j * rng.normal(
        size=(ambient_size, ambient_size)
    )
    root /= max(1.0, float(np.linalg.norm(root, 2)))

    lower_crossing = complement @ root @ projection
    upper_crossing = projection @ root @ complement
    commutator = root @ projection - projection @ root
    block_energy = float(
        np.linalg.norm(lower_crossing, "fro") ** 2
        + np.linalg.norm(upper_crossing, "fro") ** 2
    )

    detector = root.conj().T @ root
    detector_crossing = complement @ detector @ projection
    factorized = (
        upper_crossing.conj().T @ (projection @ root @ projection)
        + (complement @ root @ complement).conj().T @ lower_crossing
    )
    moving_defect = complement @ detector @ frame
    root_norm = float(np.linalg.norm(root, 2))
    bound = math.sqrt(2.0) * root_norm * float(
        np.linalg.norm(commutator, "fro")
    )

    return {
        "commutator block error": relative_error(
            commutator, lower_crossing - upper_crossing
        ),
        "block energy error": abs(
            float(np.linalg.norm(commutator, "fro") ** 2) - block_energy
        ),
        "detector factorization error": relative_error(
            detector_crossing, factorized
        ),
        "S2 bound violation": max(
            0.0, float(np.linalg.norm(detector_crossing, "fro")) - bound
        ),
        "moving isometry error": relative_error(
            float(np.linalg.norm(moving_defect, "fro")),
            float(np.linalg.norm(detector_crossing, "fro")),
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=22)
    parser.add_argument("--source-size", type=int, default=10)
    parser.add_argument("--seed", type=int, default=371)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.ambient_size, args.source_size, args.seed)
    print("Proof 371 positive-detector root-commutator certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"root commutator certificate failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("root_block_factorization=EXACT")
    print("detector_S2_reduction=PASS")
    print("raw_root_HS_norm=NOT_USED")
    print("moving_root_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
