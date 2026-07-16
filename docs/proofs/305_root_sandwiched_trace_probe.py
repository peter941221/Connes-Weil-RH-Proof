#!/usr/bin/env python3
"""Finite guard for the Proof 305 root-sandwiched trace ledger.

The probe is deliberately finite and algebraic.  It checks that a pair of
root-sandwiched kernels has the legal ``A^* B`` trace, while the CC20 ``-2``
residue is a separate root inner product.  It is not a continuous Hardy
identification, a Gate 3U estimate, or an RH proof.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def compact_root(size: int, radius: int, seed: int) -> np.ndarray:
    if 2 * radius + 1 >= size:
        raise ValueError("root support must fit inside the finite window")
    rng = np.random.default_rng(seed)
    root = np.zeros(size, dtype=complex)
    support = np.arange(-radius, radius + 1)
    values = rng.normal(size=support.size) + 1j * rng.normal(size=support.size)
    values /= np.linalg.norm(values)
    root[np.mod(support, size)] = values
    return root


def regular_kernel(nodes: np.ndarray, phase: float) -> np.ndarray:
    difference = nodes[:, None] - nodes[None, :]
    envelope = np.exp(-0.17 * difference**2)
    oscillation = 1.0 + 0.13 * np.cos(phase * (nodes[:, None] + nodes[None, :]))
    return envelope * oscillation


def run(size: int, radius: int, seed: int) -> dict[str, float]:
    nodes = np.linspace(-2.5, 2.5, size)
    left = compact_root(size, radius, seed)
    right = compact_root(size, radius, seed + 1)
    left_kernel = regular_kernel(nodes, 0.7)
    right_kernel = regular_kernel(nodes, 1.1)

    # K(y,x) -> conj(left(y)) K(y,x) right(x).
    left_factor = np.diag(np.conj(left)) @ left_kernel @ np.diag(right)
    right_factor = np.diag(np.conj(left)) @ right_kernel @ np.diag(right)

    direct_trace = np.trace(left_factor.conj().T @ right_factor)
    diagonal_trace = np.sum(
        np.diag(left_factor.conj().T @ right_factor)
    )
    row_pairing = np.sum(np.conj(left_factor) * right_factor)
    residue_pairing = -2.0 * np.vdot(right, left)
    complete_response = direct_trace + residue_pairing

    return {
        "A^*B trace readback error": relative_error(direct_trace, diagonal_trace),
        "kernel row pairing error": relative_error(direct_trace, row_pairing),
        "root atom readback error": relative_error(
            residue_pairing, -2.0 * np.vdot(right, left)
        ),
        "residue magnitude": float(abs(residue_pairing)),
        "residue omission gap": float(abs(complete_response - direct_trace)),
        "complete response magnitude": float(abs(complete_response)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=32)
    parser.add_argument("--support-radius", type=int, default=3)
    parser.add_argument("--seed", type=int, default=1305)
    args = parser.parse_args()

    metrics = run(args.size, args.support_radius, args.seed)
    print("Proof 305 finite root-sandwiched trace ledger")
    for name, value in metrics.items():
        print(f"{name}: {value:.6e}")
    print("RH=UNPROVED")

    if metrics["A^*B trace readback error"] > 1e-12:
        raise SystemExit("A^*B trace readback failed")
    if metrics["kernel row pairing error"] > 1e-12:
        raise SystemExit("kernel row pairing failed")
    if metrics["root atom readback error"] > 1e-12:
        raise SystemExit("root residue readback failed")
    if metrics["residue omission gap"] < 1e-6:
        raise SystemExit("residue omission guard did not fire")


if __name__ == "__main__":
    main()
