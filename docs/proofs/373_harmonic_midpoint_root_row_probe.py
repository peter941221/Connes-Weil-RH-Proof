"""Finite certificate for Proof 373's harmonic midpoint root consumer.

The projection path consists of exact paired-plane rotations.  The script
does not prove the continuous endpoint root theorem, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def rotated_projection(size: int, rank: int, angle: float) -> np.ndarray:
    frame = np.zeros((size, rank), dtype=complex)
    for index in range(rank):
        frame[index, index] = math.cos(angle)
        frame[rank + index, index] = math.sin(angle)
    return frame @ frame.conj().T


def canonical_midpoint(first: np.ndarray, second: np.ndarray) -> np.ndarray:
    size = first.shape[0]
    bisector = second + first - np.eye(size, dtype=complex)
    eigenvalues, eigenvectors = np.linalg.eigh(bisector)
    if float(np.min(np.abs(eigenvalues))) <= 1e-10:
        raise ValueError("midpoint bisector is singular")
    symmetry = (
        eigenvectors
        @ np.diag(np.sign(eigenvalues))
        @ eigenvectors.conj().T
    )
    return 0.5 * (np.eye(size, dtype=complex) + symmetry)


def commutator(operator: np.ndarray, projection: np.ndarray) -> np.ndarray:
    return operator @ projection - projection @ operator


def certificate(rank: int, seed: int) -> dict[str, float]:
    if rank < 2:
        raise ValueError("rank must be at least two")
    rng = np.random.default_rng(seed)
    size = 2 * rank
    primes = [3, 5, 7, 11, 13, 17]
    angles = [0.0]
    for prime in primes:
        angles.append(angles[-1] + 0.035 / math.sqrt(prime))
    projections = [rotated_projection(size, rank, angle) for angle in angles]

    root = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    root /= max(1.0, float(np.linalg.norm(root, 2)))
    detector = root.conj().T @ root
    root_norm = float(np.linalg.norm(root, 2))
    midpoint_constant = (math.sqrt(2.0) + 2.0) / 2.0

    maximum_midpoint_error = 0.0
    maximum_transfer_violation = 0.0
    maximum_detector_violation = 0.0
    weighted_detector_energy = 0.0
    endpoint_energy_bound = 0.0

    endpoint_energies = [
        float(np.linalg.norm(commutator(root, projection), "fro") ** 2)
        for projection in projections
    ]
    uniform_endpoint_energy = max(endpoint_energies)

    for index, prime in enumerate(primes):
        first = projections[index]
        second = projections[index + 1]
        midpoint = canonical_midpoint(first, second)
        expected = rotated_projection(
            size, rank, 0.5 * (angles[index] + angles[index + 1])
        )
        maximum_midpoint_error = max(
            maximum_midpoint_error, relative_error(midpoint, expected)
        )

        midpoint_root_energy = float(
            np.linalg.norm(commutator(root, midpoint), "fro") ** 2
        )
        transfer_bound = 2.0 * midpoint_constant**2 * (
            endpoint_energies[index] + endpoint_energies[index + 1]
        )
        maximum_transfer_violation = max(
            maximum_transfer_violation, midpoint_root_energy - transfer_bound
        )

        complement = np.eye(size, dtype=complex) - midpoint
        detector_crossing = complement @ detector @ midpoint
        detector_energy = float(np.linalg.norm(detector_crossing, "fro") ** 2)
        detector_bound = 2.0 * root_norm**2 * midpoint_root_energy
        maximum_detector_violation = max(
            maximum_detector_violation, detector_energy - detector_bound
        )
        weighted_detector_energy += detector_energy / (prime - 1.0)
        endpoint_energy_bound += (
            8.0
            * midpoint_constant**2
            * root_norm**2
            * uniform_endpoint_energy
            / (prime - 1.0)
        )

    return {
        "midpoint construction error": maximum_midpoint_error,
        "midpoint transfer violation": max(0.0, maximum_transfer_violation),
        "detector reduction violation": max(0.0, maximum_detector_violation),
        "harmonic consumer violation": max(
            0.0, weighted_detector_energy - endpoint_energy_bound
        ),
        "weighted detector energy": weighted_detector_energy,
        "endpoint harmonic bound": endpoint_energy_bound,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rank", type=int, default=9)
    parser.add_argument("--seed", type=int, default=373)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.rank, args.seed)
    print("Proof 373 harmonic midpoint root-row certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    exact_errors = [
        checks["midpoint construction error"],
        checks["midpoint transfer violation"],
        checks["detector reduction violation"],
        checks["harmonic consumer violation"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"midpoint root consumer failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("midpoint_root_transfer=PASS")
    print("positive_detector_reduction=PASS")
    print("harmonic_consumer=PASS")
    print("endpoint_root_uniformity=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
