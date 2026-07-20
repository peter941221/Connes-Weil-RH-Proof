"""Finite certificate for Proof 438's band-jet orientation ledger."""

from __future__ import annotations

import argparse

import numpy as np


def random_matrix(size: int, rng: np.random.Generator) -> np.ndarray:
    real = rng.normal(size=(size, size))
    imaginary = rng.normal(size=(size, size))
    return (real + 1j * imaginary) / np.sqrt(size)


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(1.0, float(np.linalg.norm(expected)))
    return float(np.linalg.norm(actual - expected)) / denominator


def positive_detector(root: np.ndarray) -> np.ndarray:
    return root.conj().T @ root


def certificate(
    size: int,
    support_rank: int,
    sonin_rank: int,
    seed: int,
) -> dict[str, float]:
    if not 0 < sonin_rank < support_rank <= size:
        raise ValueError("require 0 < sonin_rank < support_rank <= size")

    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    support = np.diag(
        np.concatenate(
            [np.ones(support_rank), np.zeros(size - support_rank)]
        )
    ).astype(complex)
    sonin = np.diag(
        np.concatenate([np.ones(sonin_rank), np.zeros(size - sonin_rank)])
    ).astype(complex)
    band = support - sonin

    raw_inverse = support @ (identity + 0.45 * random_matrix(size, rng)) @ support
    normalized_inverse = raw_inverse / max(
        1.0, float(np.linalg.norm(raw_inverse, ord=2))
    )

    proof436_pair = (
        sonin @ normalized_inverse @ band
        + band @ normalized_inverse.conj().T @ sonin
    )
    actual_band_pair = (
        band @ normalized_inverse @ sonin
        + sonin @ normalized_inverse.conj().T @ band
    )

    compression = support @ normalized_inverse @ support
    compressed_skew = compression - compression.conj().T
    orientation_commutator = sonin @ compressed_skew - compressed_skew @ sonin
    orientation_difference = proof436_pair - actual_band_pair

    commuting_root = random_matrix(size, rng)
    sonin_root = sonin @ commuting_root @ sonin
    complement_root = (identity - sonin) @ commuting_root @ (identity - sonin)
    commuting_detector = positive_detector(sonin_root + complement_root)
    noncommuting_detector = positive_detector(random_matrix(size, rng))

    fixed_commutator = (
        noncommuting_detector @ sonin - sonin @ noncommuting_detector
    )
    residual_commutator = (
        sonin @ (noncommuting_detector @ compressed_skew)
        - (noncommuting_detector @ compressed_skew) @ sonin
    )
    detector_ledger = fixed_commutator @ compressed_skew + residual_commutator

    commuting_trace_gap = abs(
        np.trace(commuting_detector @ proof436_pair)
        - np.trace(commuting_detector @ actual_band_pair)
    )
    noncommuting_trace_gap = abs(
        np.trace(noncommuting_detector @ proof436_pair)
        - np.trace(noncommuting_detector @ actual_band_pair)
    )
    finite_trace_cycle_error = abs(
        np.trace(noncommuting_detector @ orientation_commutator)
        - np.trace(fixed_commutator @ compressed_skew)
    )

    return {
        "orientation identity error": relative_error(
            orientation_difference, orientation_commutator
        ),
        "detector ledger error": relative_error(
            noncommuting_detector @ orientation_commutator,
            detector_ledger,
        ),
        "compressed skew adjoint error": float(
            np.linalg.norm(compressed_skew.conj().T + compressed_skew)
        ),
        "operator gap": float(np.linalg.norm(orientation_difference)),
        "commuting detector trace gap": float(commuting_trace_gap),
        "noncommuting detector trace gap": float(noncommuting_trace_gap),
        "finite trace cycle error": float(finite_trace_cycle_error),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=12)
    parser.add_argument("--support-rank", type=int, default=9)
    parser.add_argument("--sonin-rank", type=int, default=4)
    parser.add_argument("--seed", type=int, default=438)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    checks = certificate(
        args.size,
        args.support_rank,
        args.sonin_rank,
        args.seed,
    )
    print("Proof 438 actual band-jet orientation certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.15e}")

    if checks["orientation identity error"] > args.tolerance:
        raise RuntimeError("orientation commutator identity failed")
    if checks["detector ledger error"] > args.tolerance:
        raise RuntimeError("detector anomaly ledger failed")
    if checks["compressed skew adjoint error"] > args.tolerance:
        raise RuntimeError("compressed skew is not skew-adjoint")
    if checks["operator gap"] <= 1e-3:
        raise RuntimeError("the two paired orientations accidentally agree")
    if checks["commuting detector trace gap"] > args.tolerance:
        raise RuntimeError("commuting finite detector did not cancel the trace")
    if checks["noncommuting detector trace gap"] <= 1e-3:
        raise RuntimeError("noncommuting detector did not see the orientation")
    if checks["finite trace cycle error"] > args.tolerance:
        raise RuntimeError("finite-dimensional trace cycle failed")

    print("paired_operators=DIFFERENT")
    print("finite_commuting_detector_trace=CANCELS")
    print("infinite_trace_cycle=NOT_AUTHORIZED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
