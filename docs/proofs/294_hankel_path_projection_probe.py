#!/usr/bin/env python3
"""Certificate for Proof 294's Hankel right-path projection blocks."""

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


PROOF_293 = load_probe(
    "293_observable_two_boundary_path_probe.py",
    "proof_293_for_294",
)
PROOF_285 = PROOF_293.PROOF_285
PROOF_266 = PROOF_293.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def block_slices(
    ambient_dimension: int, band_dimension: int, horizon: int
) -> list[slice]:
    slices = [
        slice(index * ambient_dimension, (index + 1) * ambient_dimension)
        for index in range(horizon + 1)
    ]
    tail_start = (horizon + 1) * ambient_dimension
    slices.append(slice(tail_start, tail_start + band_dimension))
    return slices


def build_projection(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> dict[str, np.ndarray]:
    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 59
    )
    outer = model["E"]
    causal = model["A"]
    band_basis = model["b_basis"]
    killed = outer @ causal @ band_basis
    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    delta = identity_band - killed.conj().T @ killed
    delta = 0.5 * (delta + delta.conj().T)
    detector_band = band_basis.conj().T @ detector @ band_basis
    detector_outer = outer @ detector @ outer

    right_blocks = [
        killed @ np.linalg.matrix_power(delta, exponent)
        for exponent in range(horizon + 1)
    ]
    right_blocks.append(np.linalg.matrix_power(delta, horizon + 1))
    right_path = np.vstack(right_blocks)
    right_gram = right_path.conj().T @ right_path
    inverse_gram = np.linalg.inv(right_gram)
    path_projection = right_path @ inverse_gram @ right_path.conj().T
    observable = PROOF_293.block_diagonal(
        [detector_outer for _ in range(horizon + 1)]
        + [detector_band]
    )
    path_commutator = observable @ path_projection - path_projection @ observable

    return {
        "identity_band": identity_band,
        "outer": outer,
        "detector_outer": detector_outer,
        "detector_band": detector_band,
        "killed": killed,
        "delta": delta,
        "right_path": right_path,
        "right_gram": right_gram,
        "inverse_gram": inverse_gram,
        "path_projection": path_projection,
        "observable": observable,
        "path_commutator": path_commutator,
    }


def exact_checks(state: dict[str, np.ndarray], horizon: int) -> dict[str, float]:
    identity_band = state["identity_band"]
    detector_outer = state["detector_outer"]
    detector_band = state["detector_band"]
    killed = state["killed"]
    delta = state["delta"]
    right_gram = state["right_gram"]
    inverse_gram = state["inverse_gram"]
    path_projection = state["path_projection"]
    path_commutator = state["path_commutator"]
    ambient_dimension = detector_outer.shape[0]
    band_dimension = identity_band.shape[0]
    slices = block_slices(ambient_dimension, band_dimension, horizon)
    tail = horizon + 1

    expected_gram = (
        identity_band + np.linalg.matrix_power(delta, 2 * horizon + 3)
    ) @ np.linalg.inv(identity_band + delta)
    expected_inverse = (
        identity_band + delta
    ) @ np.linalg.inv(
        identity_band + np.linalg.matrix_power(delta, 2 * horizon + 3)
    )

    maximum_block_error = 0.0
    maximum_hankel_error = 0.0
    maximum_commutator_block_error = 0.0
    maximum_commutator_hankel_error = 0.0
    for row in range(horizon + 1):
        for column in range(horizon + 1):
            direct = path_projection[slices[row], slices[column]]
            moment = (
                killed
                @ np.linalg.matrix_power(delta, row + column)
                @ inverse_gram
                @ killed.conj().T
            )
            maximum_block_error = max(
                maximum_block_error, relative_error(direct, moment)
            )
            direct_commutator = path_commutator[
                slices[row], slices[column]
            ]
            expected_commutator = (
                detector_outer @ moment - moment @ detector_outer
            )
            maximum_commutator_block_error = max(
                maximum_commutator_block_error,
                relative_error(direct_commutator, expected_commutator),
            )

        direct_row_tail = path_projection[slices[row], slices[tail]]
        expected_row_tail = (
            killed
            @ np.linalg.matrix_power(delta, row)
            @ inverse_gram
            @ np.linalg.matrix_power(delta, horizon + 1)
        )
        maximum_block_error = max(
            maximum_block_error,
            relative_error(direct_row_tail, expected_row_tail),
        )
        direct_commutator = path_commutator[slices[row], slices[tail]]
        expected_commutator = (
            detector_outer @ expected_row_tail
            - expected_row_tail @ detector_band
        )
        maximum_commutator_block_error = max(
            maximum_commutator_block_error,
            relative_error(direct_commutator, expected_commutator),
        )

    for column in range(horizon + 1):
        direct_tail_column = path_projection[slices[tail], slices[column]]
        expected_tail_column = (
            np.linalg.matrix_power(delta, horizon + 1)
            @ inverse_gram
            @ np.linalg.matrix_power(delta, column)
            @ killed.conj().T
        )
        maximum_block_error = max(
            maximum_block_error,
            relative_error(direct_tail_column, expected_tail_column),
        )
        direct_commutator = path_commutator[slices[tail], slices[column]]
        expected_commutator = (
            detector_band @ expected_tail_column
            - expected_tail_column @ detector_outer
        )
        maximum_commutator_block_error = max(
            maximum_commutator_block_error,
            relative_error(direct_commutator, expected_commutator),
        )

    expected_tail = (
        np.linalg.matrix_power(delta, horizon + 1)
        @ inverse_gram
        @ np.linalg.matrix_power(delta, horizon + 1)
    )
    maximum_block_error = max(
        maximum_block_error,
        relative_error(
            path_projection[slices[tail], slices[tail]], expected_tail
        ),
    )
    maximum_commutator_block_error = max(
        maximum_commutator_block_error,
        relative_error(
            path_commutator[slices[tail], slices[tail]],
            detector_band @ expected_tail - expected_tail @ detector_band,
        ),
    )

    for row in range(horizon):
        for column in range(horizon):
            maximum_hankel_error = max(
                maximum_hankel_error,
                relative_error(
                    path_projection[slices[row + 1], slices[column]],
                    path_projection[slices[row], slices[column + 1]],
                ),
            )
            maximum_commutator_hankel_error = max(
                maximum_commutator_hankel_error,
                relative_error(
                    path_commutator[slices[row + 1], slices[column]],
                    path_commutator[slices[row], slices[column + 1]],
                ),
            )

    inverse_eigenvalues = np.linalg.eigvalsh(inverse_gram)
    fixed_observable = np.eye(path_projection.shape[0], dtype=complex)
    return {
        "right Gram formula error": relative_error(
            right_gram, expected_gram
        ),
        "inverse Gram formula error": relative_error(
            inverse_gram, expected_inverse
        ),
        "inverse Gram lower-bound violation": max(
            1.0 - float(np.min(inverse_eigenvalues)), 0.0
        ),
        "inverse Gram upper-bound violation": max(
            float(np.max(inverse_eigenvalues)) - 2.0, 0.0
        ),
        "path projection idempotence error": relative_error(
            path_projection @ path_projection, path_projection
        ),
        "path projection self-adjoint error": relative_error(
            path_projection.conj().T, path_projection
        ),
        "maximum projection-block formula error": maximum_block_error,
        "maximum projection Hankel error": maximum_hankel_error,
        "maximum commutator-block formula error": (
            maximum_commutator_block_error
        ),
        "maximum commutator Hankel error": maximum_commutator_hankel_error,
        "fixed-mode path-commutator error": float(
            np.linalg.norm(
                fixed_observable @ path_projection
                - path_projection @ fixed_observable
            )
        ),
        "path commutator Frobenius norm": float(
            np.linalg.norm(path_commutator, ord="fro")
        ),
        "path commutator operator norm": float(
            np.linalg.norm(path_commutator, ord=2)
        ),
    }


def block_absolute_cost(state: dict[str, np.ndarray], horizon: int) -> float:
    detector_outer = state["detector_outer"]
    identity_band = state["identity_band"]
    path_commutator = state["path_commutator"]
    slices = block_slices(
        detector_outer.shape[0], identity_band.shape[0], horizon
    )
    return sum(
        float(np.linalg.norm(path_commutator[row, column], ord="fro"))
        for row in slices
        for column in slices
    )


def growth_guard(
    multiplicity: int,
    root_radius: int,
    seed: int,
    maximum_horizon: int,
) -> dict[str, float]:
    horizons = sorted(
        set(
            horizon
            for horizon in (0, 1, 2, 4, 8, 16, maximum_horizon)
            if horizon <= maximum_horizon
        )
    )
    block_costs: list[float] = []
    operator_norms: list[float] = []
    for horizon in horizons:
        state = build_projection(
            multiplicity, root_radius, seed, horizon
        )
        block_costs.append(block_absolute_cost(state, horizon))
        operator_norms.append(
            float(np.linalg.norm(state["path_commutator"], ord=2))
        )
    return {
        "tested maximum horizon": float(max(horizons)),
        "positive block-cost growth": block_costs[-1] / block_costs[0],
        "maximum full commutator operator norm": max(operator_norms),
        "final positive block cost": block_costs[-1],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=294)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--growth-horizon", type=int, default=32)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    state = build_projection(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    checks = exact_checks(state, args.horizon)
    growth = growth_guard(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.growth_horizon,
    )

    print("identity=Hankel right-path projection")
    print("status=block structure exact; signed summation by parts open")
    for title, values in (("checks", checks), ("growth", growth)):
        print(f"{title}=BEGIN")
        for label, value in values.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}=END")

    exact_labels = tuple(
        label for label in checks if " norm" not in label
    )
    maximum_exact_error = max(float(checks[label]) for label in exact_labels)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "Hankel path-projection certificate failed: "
            f"{maximum_exact_error:.6e}"
        )

    print("right_path_projection=HANKEL_EMISSION_BLOCKS")
    print("inverse_Gram_bound=ONE_TO_TWO")
    print("blockwise_absolute_value_used=FALSE")
    print("anti_diagonal_summation_by_parts=OPEN")
    print("visible_stopped_path_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
