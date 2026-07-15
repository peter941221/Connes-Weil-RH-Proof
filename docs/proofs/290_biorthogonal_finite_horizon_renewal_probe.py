#!/usr/bin/env python3
"""Certificate for Proof 290's biorthogonal finite-horizon renewal."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
from types import ModuleType

import numpy as np


def load_probe(filename: str, module_name: str) -> ModuleType:
    path = Path(__file__).with_name(filename)
    specification = importlib.util.spec_from_file_location(module_name, path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_286 = load_probe(
    "286_first_missing_relative_mode_probe.py",
    "proof_286_for_290",
)
PROOF_285 = PROOF_286.PROOF_285
PROOF_266 = PROOF_286.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def positive_power(operator: np.ndarray, exponent: int) -> np.ndarray:
    return np.linalg.matrix_power(operator, exponent)


def block_diagonal(blocks: list[np.ndarray]) -> np.ndarray:
    row_count = sum(block.shape[0] for block in blocks)
    column_count = sum(block.shape[1] for block in blocks)
    result = np.zeros((row_count, column_count), dtype=complex)
    row_offset = 0
    column_offset = 0
    for block in blocks:
        rows, columns = block.shape
        result[
            row_offset : row_offset + rows,
            column_offset : column_offset + columns,
        ] = block
        row_offset += rows
        column_offset += columns
    return result


def build_path_model(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> tuple[dict[str, float], dict[str, np.ndarray]]:
    if horizon < 0:
        raise ValueError("horizon must be nonnegative")
    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 37
    )

    outer = model["E"]
    causal = model["A"]
    band_basis = model["b_basis"]
    killed = outer @ causal @ band_basis
    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    gamma = killed.conj().T @ killed
    delta = identity_band - gamma
    delta = 0.5 * (delta + delta.conj().T)
    detector_band = band_basis.conj().T @ detector @ band_basis
    numerator = (
        killed.conj().T @ detector @ killed - detector_band @ gamma
    )

    right_blocks = [
        killed @ positive_power(delta, power)
        for power in range(horizon + 1)
    ]
    right_blocks.append(positive_power(delta, horizon + 1))
    right_path = np.vstack(right_blocks)

    left_blocks = [killed for _ in range(horizon + 1)]
    left_blocks.append(identity_band)
    left_path = np.vstack(left_blocks)

    observable = block_diagonal(
        [detector for _ in range(horizon + 1)] + [detector_band]
    )
    right_gram = right_path.conj().T @ right_path
    expected_right_gram = (
        identity_band + positive_power(delta, 2 * horizon + 3)
    ) @ np.linalg.inv(identity_band + delta)
    inverse_right_gram = np.linalg.inv(right_gram)
    canonical_dual = right_path @ inverse_right_gram
    path_projection = (
        right_path @ inverse_right_gram @ right_path.conj().T
    )
    null_coframe = left_path - canonical_dual

    partial_renewal = sum(
        (
            numerator @ positive_power(delta, power)
            for power in range(horizon + 1)
        ),
        np.zeros_like(numerator),
    )
    path_response = (
        left_path.conj().T @ observable @ right_path - detector_band
    )
    intertwinement = observable @ right_path - right_path @ detector_band
    path_commutator = observable @ path_projection - path_projection @ observable
    canonical_split = (
        canonical_dual.conj().T @ intertwinement
        + null_coframe.conj().T @ path_commutator @ right_path
    )
    off_range_split = (
        canonical_dual.conj().T @ intertwinement
        + left_path.conj().T
        @ (np.eye(path_projection.shape[0], dtype=complex) - path_projection)
        @ intertwinement
    )

    closed_response = numerator @ np.linalg.inv(gamma)
    expected_tail = (
        numerator
        @ positive_power(delta, horizon + 1)
        @ np.linalg.inv(gamma)
    )
    fixed_observable = np.eye(observable.shape[0], dtype=complex)
    fixed_band = identity_band
    fixed_path_response = (
        left_path.conj().T @ fixed_observable @ right_path - fixed_band
    )
    fixed_intertwinement = (
        fixed_observable @ right_path - right_path @ fixed_band
    )
    fixed_commutator = (
        fixed_observable @ path_projection
        - path_projection @ fixed_observable
    )

    eigenvalues = np.linalg.eigvalsh(right_gram)
    return {
        "biorthogonality error": relative_error(
            left_path.conj().T @ right_path, identity_band
        ),
        "finite-horizon path response error": relative_error(
            path_response, partial_renewal
        ),
        "right Gram formula error": relative_error(
            right_gram, expected_right_gram
        ),
        "right Gram lower-bound violation": max(
            0.5 - float(np.min(eigenvalues)), 0.0
        ),
        "right Gram upper-bound violation": max(
            float(np.max(eigenvalues)) - 1.0, 0.0
        ),
        "canonical dual error": relative_error(
            canonical_dual.conj().T @ right_path, identity_band
        ),
        "path projection idempotence error": relative_error(
            path_projection @ path_projection, path_projection
        ),
        "path projection self-adjoint error": relative_error(
            path_projection.conj().T, path_projection
        ),
        "null coframe orthogonality error": relative_error(
            null_coframe.conj().T @ right_path,
            np.zeros_like(identity_band),
        ),
        "projected left path versus canonical dual error": relative_error(
            path_projection @ left_path, canonical_dual
        ),
        "canonical two-defect split error": relative_error(
            canonical_split, partial_renewal
        ),
        "first-missing off-range split error": relative_error(
            off_range_split, partial_renewal
        ),
        "fixed-mode response error": float(
            np.linalg.norm(fixed_path_response)
        ),
        "fixed-mode intertwinement error": float(
            np.linalg.norm(fixed_intertwinement)
        ),
        "fixed-mode path-commutator error": float(
            np.linalg.norm(fixed_commutator)
        ),
        "closed response tail error": relative_error(
            closed_response - partial_renewal, expected_tail
        ),
        "right path minimum singular value": float(
            np.min(np.linalg.svd(right_path, compute_uv=False))
        ),
        "right path operator norm": float(
            np.linalg.norm(right_path, ord=2)
        ),
        "canonical dual operator norm": float(
            np.linalg.norm(canonical_dual, ord=2)
        ),
        "left path operator norm": float(np.linalg.norm(left_path, ord=2)),
        "null coframe operator norm": float(
            np.linalg.norm(null_coframe, ord=2)
        ),
    }, {
        "gamma": gamma,
        "delta": delta,
        "killed": killed,
    }


def growth_guard(
    state: dict[str, np.ndarray], maximum_horizon: int
) -> dict[str, float]:
    killed = state["killed"]
    delta = state["delta"]
    band_dimension = delta.shape[0]
    identity_band = np.eye(band_dimension, dtype=complex)
    horizons = [0, 1, 2, 4, 8, maximum_horizon]
    horizons = sorted(set(value for value in horizons if value <= maximum_horizon))
    left_norms: list[float] = []
    right_norms: list[float] = []
    dual_norms: list[float] = []
    for horizon in horizons:
        right_path = np.vstack(
            [
                killed @ positive_power(delta, power)
                for power in range(horizon + 1)
            ]
            + [positive_power(delta, horizon + 1)]
        )
        left_path = np.vstack(
            [killed for _ in range(horizon + 1)] + [identity_band]
        )
        right_gram = right_path.conj().T @ right_path
        canonical_dual = right_path @ np.linalg.inv(right_gram)
        left_norms.append(float(np.linalg.norm(left_path, ord=2)))
        right_norms.append(float(np.linalg.norm(right_path, ord=2)))
        dual_norms.append(float(np.linalg.norm(canonical_dual, ord=2)))

    return {
        "tested maximum horizon": float(max(horizons)),
        "left path norm growth": left_norms[-1] / left_norms[0],
        "maximum right path norm": max(right_norms),
        "maximum canonical dual norm": max(dual_norms),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=290)
    parser.add_argument("--horizon", type=int, default=8)
    parser.add_argument("--growth-horizon", type=int, default=32)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--growth-floor", type=float, default=2.0)
    args = parser.parse_args()

    path_checks, state = build_path_model(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    growth = growth_guard(state, args.growth_horizon)

    print("identity=biorthogonal finite-horizon renewal colligation")
    print("status=ordered finite path exact; source commutator bound open")
    for title, checks in (("path", path_checks), ("growth", growth)):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_labels = (
        "biorthogonality error",
        "finite-horizon path response error",
        "right Gram formula error",
        "right Gram lower-bound violation",
        "right Gram upper-bound violation",
        "canonical dual error",
        "path projection idempotence error",
        "path projection self-adjoint error",
        "null coframe orthogonality error",
        "projected left path versus canonical dual error",
        "canonical two-defect split error",
        "first-missing off-range split error",
        "fixed-mode response error",
        "fixed-mode intertwinement error",
        "fixed-mode path-commutator error",
        "closed response tail error",
    )
    maximum_exact_error = max(float(path_checks[label]) for label in exact_labels)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "biorthogonal renewal certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if float(path_checks["right path operator norm"]) > 1.0 + args.tolerance:
        raise SystemExit("right path lost its contraction bound")
    if (
        float(path_checks["canonical dual operator norm"])
        > 2.0**0.5 + args.tolerance
    ):
        raise SystemExit("canonical dual lost its sqrt(2) bound")
    if float(growth["left path norm growth"]) < args.growth_floor:
        raise SystemExit("left-path growth guard was not separated")

    print("finite_horizon_renewal=EXACT_PATH_PAIRING")
    print("right_path_conditioning=UNIFORM_SQRT2")
    print("canonical_dual=UNIFORM_SQRT2")
    print("detector_bulk=ELIMINATED")
    print("null_coframe_norm_used=FALSE")
    print("source_path_commutator_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
