"""Finite certificate for Proof 400's relative-trace cocycle collapse."""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def random_invertible(size: int, rng: np.random.Generator) -> np.ndarray:
    unitary_left, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    unitary_right, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    singular_values = 0.35 + 0.55 * rng.random(size)
    return unitary_left @ np.diag(singular_values) @ unitary_right


def certificate(size: int, steps: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    forwards: list[np.ndarray] = []
    reverses: list[np.ndarray] = []
    scales: list[float] = []
    compressions = [
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
        for _ in range(steps + 1)
    ]

    for index in range(steps):
        forward = random_invertible(size, rng)
        scale = (0.17 + 0.08 * index) / (1.0 + 0.04 * index)
        reverse = scale * np.linalg.inv(forward)
        forwards.append(forward)
        reverses.append(reverse)
        scales.append(scale)

    local = [
        forwards[index]
        @ compressions[index + 1]
        @ reverses[index]
        - scales[index] * compressions[index]
        for index in range(steps)
    ]

    gamma = np.eye(size, dtype=complex)
    lamb = np.eye(size, dtype=complex)
    scale_product = 1.0
    maximum_prefix_pair_error = 0.0
    maximum_term_trace_error = 0.0
    telescoped = np.zeros((size, size), dtype=complex)

    for index in range(steps):
        scale_after = float(np.prod(scales[index + 1 :]))
        term = scale_after * gamma @ local[index] @ lamb
        telescoped += term
        expected_trace = (
            scale_after * float(np.prod(scales[:index])) * np.trace(local[index])
        )
        maximum_term_trace_error = max(
            maximum_term_trace_error,
            relative_error(np.trace(term), expected_trace),
        )
        gamma = gamma @ forwards[index]
        lamb = reverses[index] @ lamb
        scale_product *= scales[index]
        maximum_prefix_pair_error = max(
            maximum_prefix_pair_error,
            relative_error(
                gamma @ lamb,
                scale_product * np.eye(size, dtype=complex),
            ),
        )

    complete = (
        gamma @ compressions[-1] @ lamb
        - scale_product * compressions[0]
    )
    local_trace_sum = sum(
        np.trace(local[index]) / scales[index] for index in range(steps)
    )
    endpoint = (
        gamma @ compressions[-1] @ np.linalg.inv(gamma)
        - compressions[0]
    )

    return {
        "maximum prefix pair error": maximum_prefix_pair_error,
        "operator telescope error": relative_error(complete, telescoped),
        "maximum term trace collapse error": maximum_term_trace_error,
        "complete trace collapse error": relative_error(
            np.trace(complete) / scale_product,
            local_trace_sum,
        ),
        "endpoint cocycle readback error": relative_error(
            np.trace(endpoint),
            local_trace_sum,
        ),
        "scale product": scale_product,
        "complete numerator norm": float(np.linalg.norm(complete, 2)),
        "local signed trace magnitude": float(abs(local_trace_sum)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=7)
    parser.add_argument("--steps", type=int, default=9)
    parser.add_argument("--seed", type=int, default=400)
    parser.add_argument("--tolerance", type=float, default=2e-8)
    args = parser.parse_args()

    checks = certificate(args.size, args.steps, args.seed)
    print("Proof 400 relative-trace cocycle collapse certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum prefix pair error",
        "operator telescope error",
        "maximum term trace collapse error",
        "complete trace collapse error",
        "endpoint cocycle readback error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"relative-trace collapse failed: {maximum_error:.3e}")
    if checks["scale product"] >= 1e-3:
        raise RuntimeError("test cascade does not expose a small scalar product")
    if checks["local signed trace magnitude"] <= 1e-6:
        raise RuntimeError("local signed trace is accidentally trivial")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("complete_prefix_conditioning=ELIMINATED_INSIDE_TRACE")
    print("signed_local_cocycle=EXACT")
    print("uniform_local_cocycle_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
