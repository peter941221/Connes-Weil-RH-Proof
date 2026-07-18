"""Finite topology certificate for Proof 406's model-space limit."""

from __future__ import annotations

import argparse

import numpy as np


def trace_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.svd(matrix, compute_uv=False).sum())


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def circle_nodes(size: int) -> np.ndarray:
    return np.exp(2j * np.pi * np.arange(size) / size)


def model_projection(nodes: np.ndarray, zeros: np.ndarray) -> np.ndarray:
    columns = []
    for zero in zeros:
        kernel = np.sqrt(1.0 - abs(zero) ** 2) / (1.0 - np.conj(zero) * nodes)
        columns.append(kernel / np.sqrt(nodes.size))
    raw = np.column_stack(columns)
    frame, _ = np.linalg.qr(raw)
    return frame @ frame.conj().T


def certificate(size: int, reference_rank: int) -> dict[str, float]:
    nodes = circle_nodes(size)
    indices = np.arange(1, reference_rank + 1)
    radii = 1.0 - 0.42 / (indices + 1.0) ** 2
    angles = 0.31 + 0.73 * indices / (reference_rank + 1.0)
    zeros = radii * np.exp(1j * angles)

    detector_values = (
        0.8
        + 0.17 * np.cos(np.angle(nodes))
        + 0.09 * np.cos(2.0 * np.angle(nodes))
    )
    transport_values = np.exp(0.23j * np.sin(np.angle(nodes)))
    detector = np.diag(detector_values.astype(complex))
    transport = np.diag(transport_values)

    reference = model_projection(nodes, zeros)
    identity = np.eye(size, dtype=complex)
    reference_commutator = detector @ reference - reference @ detector
    reference_semicommutator = (
        reference
        @ detector
        @ (identity - reference)
        @ transport
        @ reference
    )

    ranks = sorted(
        {
            max(2, reference_rank // 4),
            max(3, reference_rank // 2),
            max(4, 3 * reference_rank // 4),
            reference_rank - 1,
        }
    )
    commutator_errors = []
    semicommutator_errors = []
    trace_errors = []
    algebra_errors = []

    for rank in ranks:
        projection = model_projection(nodes, zeros[:rank])
        commutator = detector @ projection - projection @ detector
        semicommutator = (
            projection
            @ detector
            @ (identity - projection)
            @ transport
            @ projection
        )
        commutator_form = (
            -projection
            @ commutator
            @ (identity - projection)
            @ transport
            @ projection
        )
        algebra_errors.append(relative_error(semicommutator, commutator_form))
        commutator_errors.append(trace_norm(commutator - reference_commutator))
        semicommutator_errors.append(
            trace_norm(semicommutator - reference_semicommutator)
        )
        trace_errors.append(
            float(abs(np.trace(semicommutator - reference_semicommutator)))
        )

    return {
        "maximum algebra error": max(algebra_errors),
        "initial commutator S1 error": commutator_errors[0],
        "final commutator S1 error": commutator_errors[-1],
        "initial semicommutator S1 error": semicommutator_errors[0],
        "final semicommutator S1 error": semicommutator_errors[-1],
        "initial scalar trace error": trace_errors[0],
        "final scalar trace error": trace_errors[-1],
        "commutator contraction ratio": (
            commutator_errors[-1] / max(commutator_errors[0], 1e-15)
        ),
        "semicommutator contraction ratio": (
            semicommutator_errors[-1]
            / max(semicommutator_errors[0], 1e-15)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=320)
    parser.add_argument("--reference-rank", type=int, default=20)
    parser.add_argument("--tolerance", type=float, default=2e-12)
    args = parser.parse_args()

    checks = certificate(args.size, args.reference_rank)
    print("Proof 406 standard model-limit certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    if checks["maximum algebra error"] > args.tolerance:
        raise RuntimeError("ordered semicommutator algebra failed")
    if checks["commutator contraction ratio"] >= 0.8:
        raise RuntimeError("commutator S1 approximation did not improve")
    if checks["semicommutator contraction ratio"] >= 0.8:
        raise RuntimeError("semicommutator S1 approximation did not improve")

    print("standard_model_first_jet_limit=TRACE_NORM")
    print("burnol_route_intertwinement=NOT_PROVED")
    print("raw_euler_commutator_ideal=NOT_REQUIRED")
    print("uniform_mixed_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
