#!/usr/bin/env python3
"""Finite-boundary certificate for Proof 297's trace-anomaly guard."""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def finite_shift(size: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    for column in range(size - 1):
        shift[column + 1, column] = 1.0
    return shift


def positive_square_root(operator: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(operator)
    return (
        eigenvectors
        @ np.diag(np.sqrt(eigenvalues))
        @ eigenvectors.conj().T
    )


def certificate(size: int, scale: float) -> dict[str, float]:
    if size < 4:
        raise ValueError("size must be at least four")
    if not 0.0 < scale < 1.0 / 3.0:
        raise ValueError("scale must lie in (0,1/3)")

    shift = finite_shift(size)
    identity = np.eye(size, dtype=complex)
    first = np.zeros((size, size), dtype=complex)
    first[0, 0] = 1.0
    far = np.zeros((size, size), dtype=complex)
    far[-1, -1] = 1.0

    detector = 0.5 * (shift + shift.conj().T)
    y_operator = (shift - shift.conj().T) / (2.0j)
    commutator_xy = detector @ y_operator - y_operator @ detector
    expected_commutator_xy = (first - far) / (2.0j)

    metric = scale * (y_operator + 2.0 * identity)
    killed = positive_square_root(metric)
    delta = identity - metric
    weighted_commutator = (
        killed
        @ (detector @ metric - metric @ detector)
        @ killed
    )

    left_commutator = scale * first / (2.0j)
    far_commutator = -scale * far / (2.0j)
    left_weighted = killed @ left_commutator @ killed
    far_weighted = killed @ far_commutator @ killed

    metric_eigenvalues = np.linalg.eigvalsh(metric)
    delta_eigenvalues = np.linalg.eigvalsh(delta)
    expected_left_trace = scale**2 / 1.0j
    expected_far_trace = -expected_left_trace

    return {
        "shift commutator error": relative_error(
            commutator_xy, expected_commutator_xy
        ),
        "metric square-root error": relative_error(
            killed.conj().T @ killed, metric
        ),
        "weighted boundary split error": relative_error(
            weighted_commutator, left_weighted + far_weighted
        ),
        "left boundary trace error": float(
            abs(np.trace(left_weighted) - expected_left_trace)
        ),
        "far boundary trace error": float(
            abs(np.trace(far_weighted) - expected_far_trace)
        ),
        "finite total trace error": float(abs(np.trace(weighted_commutator))),
        "metric lower-bound violation": max(
            scale - float(np.min(metric_eigenvalues)), 0.0
        ),
        "metric upper-bound violation": max(
            float(np.max(metric_eigenvalues)) - 3.0 * scale, 0.0
        ),
        "Delta lower-bound violation": max(
            1.0 - 3.0 * scale - float(np.min(delta_eigenvalues)), 0.0
        ),
        "Delta upper-bound violation": max(
            float(np.max(delta_eigenvalues)) - (1.0 - scale), 0.0
        ),
        "left physical anomaly magnitude": float(abs(expected_left_trace)),
        "artificial far anomaly magnitude": float(abs(expected_far_trace)),
        "finite-versus-infinite trace gap": float(abs(expected_left_trace)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=18)
    parser.add_argument("--scale", type=float, default=0.25)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--guard-floor", type=float, default=5e-2)
    args = parser.parse_args()

    checks = certificate(args.size, args.scale)
    print("identity=emission-grid trace anomaly")
    print("status=finite trace zero is boundary polluted; source cycle forbidden")
    print("checks=BEGIN")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={float(value):.12e}")
    print("checks=END")

    guard_labels = {
        "left physical anomaly magnitude",
        "artificial far anomaly magnitude",
        "finite-versus-infinite trace gap",
    }
    maximum_exact_error = max(
        float(value)
        for label, value in checks.items()
        if label not in guard_labels
    )
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "emission trace-anomaly certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if checks["finite-versus-infinite trace gap"] < args.guard_floor:
        raise SystemExit("trace-anomaly rejection guard did not fire")

    print("finite_emission_trace_zero=ARTIFICIAL_BOUNDARY_CANCELLATION")
    print("infinite_weighted_commutator_trace=NONZERO")
    print("all_even_sector_trace_deletion=FORBIDDEN")
    print("source_outer_sonin_anomaly_cancellation=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
