#!/usr/bin/env python3
"""Exact finite-dimensional checks for Proof 774's algebraic guard."""

from __future__ import annotations

import numpy as np


def require_close(name: str, actual: np.ndarray | complex | float,
                  expected: np.ndarray | complex | float, tolerance: float) -> float:
    error = float(np.max(np.abs(np.asarray(actual) - np.asarray(expected))))
    if error > tolerance:
        raise AssertionError(f"{name}: error {error:.3e} exceeds {tolerance:.3e}")
    return error


def main() -> None:
    tolerance = 1.0e-12
    projection = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    detector = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    commutator = projection @ detector - detector @ projection
    inclusion = np.array([1.0, 0.0], dtype=np.complex128)
    forward = np.array([0.0, 0.0], dtype=np.complex128)

    maximum_error = 0.0
    minimum_growth_gap = float("inf")
    for scale in (0.25, 1.0, 7.0, 31.0):
        residual = np.array([0.0, scale], dtype=np.complex128)
        old_scalar = np.vdot(inclusion, commutator @ residual) - np.vdot(
            forward, commutator @ inclusion
        )
        directed_scalar = np.vdot(inclusion, commutator @ (residual + forward))

        maximum_error = max(maximum_error, require_close(
            f"real directed identity at t={scale}", old_scalar.real,
            directed_scalar.real, tolerance
        ))
        maximum_error = max(maximum_error, require_close(
            f"residual off Sonin range at t={scale}", projection @ residual,
            np.zeros(2, dtype=np.complex128), tolerance
        ))
        maximum_error = max(maximum_error, require_close(
            f"inclusion adjoint residual at t={scale}", np.vdot(inclusion, residual),
            0.0, tolerance
        ))
        maximum_error = max(maximum_error, require_close(
            f"forward contraction at t={scale}", np.linalg.norm(forward), 0.0,
            tolerance
        ))
        maximum_error = max(maximum_error, require_close(
            f"skew adjoint commutator at t={scale}", commutator.conj().T,
            -commutator, tolerance
        ))
        minimum_growth_gap = min(
            minimum_growth_gap, abs(old_scalar.real) / scale
        )

    print("+----------------------------------------------+-------------------------+")
    print("| check                                        | result                  |")
    print("+----------------------------------------------+-------------------------+")
    print("| real directed crossing identity             | PASS                    |")
    print("| projection and inclusion orthogonality      | PASS                    |")
    print("| forward contraction and skew adjointness    | PASS                    |")
    print(f"| maximum algebra error                       | {maximum_error:.2e}                |")
    growth_result = f"{minimum_growth_gap:.12g}"
    print("| minimum unbounded-growth ratio              | " +
          growth_result.ljust(24) + "|")
    print("+----------------------------------------------+-------------------------+")


if __name__ == "__main__":
    main()
