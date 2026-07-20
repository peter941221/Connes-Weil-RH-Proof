"""Finite certificate for Proof 437's paired first-jet decomposition."""

from __future__ import annotations

import argparse

import numpy as np


def projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    numerator = float(np.linalg.norm(np.asarray(actual) - np.asarray(expected)))
    denominator = max(1.0, float(np.linalg.norm(np.asarray(expected))))
    return numerator / denominator


def random_matrix(size: int, rng: np.random.Generator) -> np.ndarray:
    return rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))


def certificate(
    size: int,
    band_rank: int,
    inner_rank: int,
    seed: int,
) -> dict[str, float]:
    if band_rank + inner_rank > size:
        raise ValueError("band and inner ranks exceed the ambient dimension")

    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    band_columns = identity[:, :band_rank]
    inner_columns = identity[:, band_rank : band_rank + inner_rank]
    band = band_columns @ band_columns.conj().T
    inner = inner_columns @ inner_columns.conj().T
    support = band + inner

    raw_generator = random_matrix(size, rng)
    generator = support @ raw_generator @ support
    root = random_matrix(size, rng)
    detector = root.conj().T @ root

    exact_errors: list[float] = []
    single_linear_ratios: list[float] = []
    paired_linear_ratios: list[float] = []
    paired_quadratic_ratios: list[float] = []
    scalar_errors: list[float] = []

    steps = [2.0**-power for power in range(2, 15)]
    for step in steps:
        transport = support + step * generator
        frame = transport @ band_columns
        gram = frame.conj().T @ frame
        gram_inverse = (
            band_columns @ np.linalg.solve(gram, band_columns.conj().T)
        )
        target = projection(frame)

        forward = inner @ transport @ band
        reverse = band @ transport.conj().T @ inner
        paired = forward + reverse

        coframe_defect = (
            gram_inverse @ band @ transport.conj().T @ band - band
        )
        reverse_coframe_defect = (
            band @ transport @ band @ gram_inverse - band
        )
        missed = (support - target) @ band
        quadratic_remainder = (
            forward @ coframe_defect
            + reverse_coframe_defect @ reverse
            + forward @ gram_inverse @ reverse
            - missed.conj().T @ missed
        )

        endpoint = target - band
        exact_errors.append(relative_error(endpoint, paired + quadratic_remainder))

        single_residual = endpoint - forward
        paired_residual = endpoint - paired
        single_linear_ratios.append(float(np.linalg.norm(single_residual) / step))
        paired_linear_ratios.append(float(np.linalg.norm(paired_residual) / step))
        paired_quadratic_ratios.append(
            float(np.linalg.norm(paired_residual) / (step * step))
        )

        oriented_detector_corner = np.trace(
            band @ detector @ inner @ transport @ band
        )
        paired_detector_trace = np.trace(detector @ paired)
        scalar_errors.append(
            relative_error(
                paired_detector_trace,
                2.0 * np.real(oriented_detector_corner),
            )
        )

    smallest_single_linear = single_linear_ratios[-1]
    smallest_paired_linear = paired_linear_ratios[-1]
    paired_quadratic_spread = max(paired_quadratic_ratios[-4:]) / min(
        paired_quadratic_ratios[-4:]
    )

    return {
        "maximum exact decomposition error": max(exact_errors),
        "maximum paired scalar error": max(scalar_errors),
        "smallest-step single residual over t": smallest_single_linear,
        "smallest-step paired residual over t": smallest_paired_linear,
        "paired residual quadratic ratio spread": paired_quadratic_spread,
        "single-to-paired linear ratio": (
            smallest_single_linear / max(smallest_paired_linear, 1e-30)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=14)
    parser.add_argument("--band-rank", type=int, default=5)
    parser.add_argument("--inner-rank", type=int, default=4)
    parser.add_argument("--seed", type=int, default=437)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    checks = certificate(args.size, args.band_rank, args.inner_rank, args.seed)
    print("Proof 437 paired first-jet certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    if checks["maximum exact decomposition error"] > args.tolerance:
        raise RuntimeError("paired endpoint decomposition failed")
    if checks["maximum paired scalar error"] > args.tolerance:
        raise RuntimeError("paired scalar is not twice the real oriented trace")
    if checks["smallest-step single residual over t"] <= 1e-3:
        raise RuntimeError("one-sided subtraction unexpectedly removed the linear term")
    if checks["smallest-step paired residual over t"] >= 1e-2:
        raise RuntimeError("paired subtraction did not remove the linear term")
    if checks["paired residual quadratic ratio spread"] >= 1.15:
        raise RuntimeError("paired residual is not in the quadratic regime")

    print("one_sided_remainder=LINEAR")
    print("paired_remainder=QUADRATIC")
    print("reflected_outer_as_adjoint_jet=REJECTED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
