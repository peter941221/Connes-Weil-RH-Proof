#!/usr/bin/env python3
"""Finite checks for Proof 773's zero-transfer visibility obstruction."""

from __future__ import annotations

import numpy as np


def normalize(vector: np.ndarray) -> np.ndarray:
    return vector / np.linalg.norm(vector)


def projection(vector: np.ndarray) -> np.ndarray:
    unit = normalize(vector)
    return np.outer(unit, unit.conj())


def complement_vector(unit: np.ndarray) -> np.ndarray:
    return np.array([-unit[1].conj(), unit[0].conj()], dtype=np.complex128)


def inverse_square_root(positive: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(positive)
    return eigenvectors @ np.diag(1.0 / np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def canonical_midpoint(old: np.ndarray, new: np.ndarray) -> np.ndarray:
    identity = np.eye(2, dtype=np.complex128)
    bisector = old + new - identity
    symmetry = bisector @ inverse_square_root(bisector @ bisector)
    return 0.5 * (identity + symmetry)


def zero_transfer_step(old_unit: np.ndarray, a: float) -> dict[str, np.ndarray | complex | float]:
    s = np.sqrt(1.0 - a * a)
    old_complement = complement_vector(old_unit)
    basis = np.column_stack([old_unit, old_complement])
    local_unitary = np.array([[a, -s], [s, a]], dtype=np.complex128)
    unitary = basis @ local_unitary @ basis.conj().T
    transport = np.eye(2, dtype=np.complex128) - a * unitary
    new_unit = normalize(np.linalg.solve(transport, old_unit))

    u00 = np.vdot(old_unit, unitary @ old_unit)
    u01 = np.vdot(old_unit, unitary @ old_complement)
    u10 = np.vdot(old_complement, unitary @ old_unit)
    u11 = np.vdot(old_complement, unitary @ old_complement)
    graph = a * u10 / (1.0 - a * u11)
    transfer = u00 + a * u01 * u10 / (1.0 - a * u11)
    expected_new = normalize(old_unit + graph * old_complement)

    return {
        "unitary": unitary,
        "transport": transport,
        "new_unit": new_unit,
        "transfer": transfer,
        "graph": graph,
        "expected_new": expected_new,
        "range_sine": abs(graph) / np.sqrt(1.0 + abs(graph) ** 2),
    }


def check_prime_pair(first_prime: int, second_prime: int) -> dict[str, float]:
    a = 1.0 / np.sqrt(float(first_prime))
    b = 1.0 / np.sqrt(float(second_prime))
    first = zero_transfer_step(np.array([1.0, 0.0], dtype=np.complex128), a)
    second = zero_transfer_step(first["new_unit"], b)

    p1 = projection(first["new_unit"])
    p2 = projection(second["new_unit"])
    midpoint = canonical_midpoint(p1, p2)
    complement = np.eye(2, dtype=np.complex128) - midpoint
    difference = p2 - p1
    innovation = complement @ difference @ midpoint

    midpoint_values, midpoint_vectors = np.linalg.eigh(midpoint)
    u = midpoint_vectors[:, np.argmax(midpoint_values)]
    v = midpoint_vectors[:, np.argmin(midpoint_values)]
    coefficient = np.vdot(v, innovation @ u)
    v = v * np.exp(1j * np.angle(coefficient))
    coefficient = np.vdot(v, innovation @ u)

    root = np.outer(u, u + v)
    detector = root.conj().T @ root
    corner = midpoint @ detector @ complement
    expected_corner = np.outer(u, v.conj())
    response = np.trace(detector @ difference)
    paired_response = 2.0 * np.real(np.trace(corner @ innovation))

    zero_prefix = complex(first["transfer"])
    impossible_factor = zero_prefix * root

    return {
        "unitarity_error": np.linalg.norm(first["unitary"].conj().T @ first["unitary"] - np.eye(2)),
        "transport_det_error": abs(np.linalg.det(first["transport"]) - (1.0 - a * a)),
        "first_transfer_zero_error": abs(first["transfer"]),
        "second_transfer_zero_error": abs(second["transfer"]),
        "first_graph_range_error": min(
            np.linalg.norm(first["new_unit"] - first["expected_new"]),
            np.linalg.norm(first["new_unit"] + first["expected_new"]),
        ),
        "range_sine_error": abs(float(first["range_sine"]) - a),
        "innovation_split_error": np.linalg.norm(difference - innovation - innovation.conj().T),
        "innovation_size_error": abs(abs(coefficient) - b),
        "corner_error": np.linalg.norm(corner - expected_corner),
        "root_rank_error": abs(float(np.linalg.matrix_rank(root)) - 1.0),
        "midpoint_trace_error": abs(response - paired_response),
        "response_size_error": abs(abs(response) - 2.0 * b),
        "zero_prefix_factor_norm": np.linalg.norm(impossible_factor),
        "nonzero_corner_norm": np.linalg.norm(corner),
        "obstruction_gap": np.linalg.norm(corner - impossible_factor),
    }


def main() -> None:
    tolerance = 5e-11
    checks = {
        pair: check_prime_pair(*pair)
        for pair in ((2, 3), (3, 5), (5, 7))
    }

    for pair, result in checks.items():
        print(f"primes={pair[0]},{pair[1]}")
        for name, value in result.items():
            print(f"{name:30s} {value:.12e}")

    error_names = {
        "unitarity_error",
        "transport_det_error",
        "first_transfer_zero_error",
        "second_transfer_zero_error",
        "first_graph_range_error",
        "range_sine_error",
        "innovation_split_error",
        "innovation_size_error",
        "corner_error",
        "root_rank_error",
        "midpoint_trace_error",
        "response_size_error",
        "zero_prefix_factor_norm",
    }
    maximum_error = max(
        value
        for result in checks.values()
        for name, value in result.items()
        if name in error_names
    )
    minimum_corner = min(result["nonzero_corner_norm"] for result in checks.values())
    minimum_gap = min(result["obstruction_gap"] for result in checks.values())

    print(f"maximum algebra error          {maximum_error:.12e}")
    print(f"minimum nonzero corner norm    {minimum_corner:.12e}")
    print(f"minimum obstruction gap        {minimum_gap:.12e}")

    if maximum_error > tolerance:
        raise SystemExit("zero-transfer Julia construction check failed")
    if minimum_corner <= 0.5:
        raise SystemExit("completed corner unexpectedly vanished")
    if minimum_gap <= 0.5:
        raise SystemExit("zero prefix did not obstruct the factorization")


if __name__ == "__main__":
    main()
