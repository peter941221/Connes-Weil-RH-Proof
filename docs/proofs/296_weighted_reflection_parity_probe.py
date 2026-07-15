#!/usr/bin/env python3
"""Certificate for Proof 296's weighted reflection parity decomposition."""

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


PROOF_295 = load_probe(
    "295_reflected_hankel_divided_difference_probe.py",
    "proof_295_for_296",
)
PROOF_294 = PROOF_295.PROOF_294


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def build_weighted_path(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> dict[str, np.ndarray]:
    if horizon < 2:
        raise ValueError("horizon must be at least two")
    state = PROOF_294.build_projection(
        multiplicity, root_radius, seed, horizon
    )
    killed = state["killed"]
    delta = state["delta"]
    inverse_gram = state["inverse_gram"]
    identity_band = state["identity_band"]
    path_length = horizon + 1

    right_path = state["right_path"]
    left_path = np.vstack(
        [killed for _ in range(path_length)] + [identity_band]
    )
    canonical_dual = right_path @ inverse_gram
    null_coframe = left_path - canonical_dual

    return {
        **state,
        "left_path": left_path,
        "canonical_dual": canonical_dual,
        "null_coframe": null_coframe,
        "path_length": np.array(path_length),
    }


def certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> dict[str, float]:
    state = build_weighted_path(
        multiplicity, root_radius, seed, horizon
    )
    killed = state["killed"]
    delta = state["delta"]
    inverse_gram = state["inverse_gram"]
    identity_band = state["identity_band"]
    detector_outer = state["detector_outer"]
    detector_band = state["detector_band"]
    path_commutator = state["path_commutator"]
    right_path = state["right_path"]
    left_path = state["left_path"]
    null_coframe = state["null_coframe"]
    path_length = int(state["path_length"])
    tail = path_length
    slices = PROOF_294.block_slices(
        detector_outer.shape[0], identity_band.shape[0], horizon
    )

    expected_null_coframe = np.vstack(
        [
            killed
            @ (
                identity_band
                - np.linalg.matrix_power(delta, index) @ inverse_gram
            )
            for index in range(path_length)
        ]
        + [
            identity_band
            - np.linalg.matrix_power(delta, path_length) @ inverse_gram
        ]
    )

    off_range_owner = (
        null_coframe.conj().T @ path_commutator @ right_path
    )
    direct_block_sum = np.zeros_like(off_range_owner)
    interior_owner = np.zeros_like(off_range_owner)
    boundary_owner = np.zeros_like(off_range_owner)
    sectors = [np.zeros_like(off_range_owner) for _ in range(4)]

    maximum_parity_orbit_error = 0.0
    maximum_left_filter_error = 0.0
    maximum_right_filter_error = 0.0
    maximum_commutator_filter_error = 0.0

    for row in range(path_length + 1):
        left_block = null_coframe[slices[row], :].conj().T
        for column in range(path_length + 1):
            right_block = right_path[slices[column], :]
            commutator_block = path_commutator[
                slices[row], slices[column]
            ]
            term = left_block @ commutator_block @ right_block
            direct_block_sum += term

            if 1 <= row < path_length and 1 <= column < path_length:
                interior_owner += term
                reflected_row = path_length - row
                reflected_column = path_length - column

                left_reflected = null_coframe[
                    slices[reflected_row], :
                ].conj().T
                right_reflected = right_path[slices[reflected_column], :]
                commutator_reflected = path_commutator[
                    slices[reflected_row], slices[reflected_column]
                ]

                left_plus = 0.5 * (left_block + left_reflected)
                left_minus = 0.5 * (left_block - left_reflected)
                right_plus = 0.5 * (right_block + right_reflected)
                right_minus = 0.5 * (right_block - right_reflected)
                commutator_plus = 0.5 * (
                    commutator_block + commutator_reflected
                )
                commutator_minus = 0.5 * (
                    commutator_block - commutator_reflected
                )

                parity_terms = (
                    left_plus @ commutator_plus @ right_plus,
                    left_plus @ commutator_minus @ right_minus,
                    left_minus @ commutator_plus @ right_minus,
                    left_minus @ commutator_minus @ right_plus,
                )
                for index, parity_term in enumerate(parity_terms):
                    sectors[index] += parity_term

                reflected_term = (
                    left_reflected
                    @ commutator_reflected
                    @ right_reflected
                )
                maximum_parity_orbit_error = max(
                    maximum_parity_orbit_error,
                    relative_error(
                        term + reflected_term,
                        2.0 * sum(parity_terms, np.zeros_like(term)),
                    ),
                )

                function_row = PROOF_295.kernel_matrix(
                    delta, path_length, row
                )
                function_reflected_row = PROOF_295.kernel_matrix(
                    delta, path_length, reflected_row
                )
                expected_left_plus = (
                    identity_band
                    - 0.5 * (function_row + function_reflected_row)
                ) @ killed.conj().T
                expected_left_minus = 0.5 * (
                    function_reflected_row - function_row
                ) @ killed.conj().T
                maximum_left_filter_error = max(
                    maximum_left_filter_error,
                    relative_error(left_plus, expected_left_plus),
                    relative_error(left_minus, expected_left_minus),
                )

                expected_right_plus = 0.5 * killed @ (
                    np.linalg.matrix_power(delta, column)
                    + np.linalg.matrix_power(delta, reflected_column)
                )
                expected_right_minus = 0.5 * killed @ (
                    np.linalg.matrix_power(delta, column)
                    - np.linalg.matrix_power(delta, reflected_column)
                )
                maximum_right_filter_error = max(
                    maximum_right_filter_error,
                    relative_error(right_plus, expected_right_plus),
                    relative_error(right_minus, expected_right_minus),
                )

                exponent = row + column
                beta = PROOF_295.beta_matrix(
                    delta, path_length, exponent
                )
                expected_commutator_plus = 0.5 * commutator(
                    detector_outer,
                    killed @ (2.0 * identity_band - beta) @ killed.conj().T,
                )
                kernel_difference = (
                    PROOF_295.kernel_matrix(
                        delta, path_length, exponent
                    )
                    - PROOF_295.kernel_matrix(
                        delta,
                        path_length,
                        2 * path_length - exponent,
                    )
                )
                expected_commutator_minus = 0.5 * commutator(
                    detector_outer,
                    killed @ kernel_difference @ killed.conj().T,
                )
                maximum_commutator_filter_error = max(
                    maximum_commutator_filter_error,
                    relative_error(
                        commutator_plus, expected_commutator_plus
                    ),
                    relative_error(
                        commutator_minus, expected_commutator_minus
                    ),
                )
            else:
                boundary_owner += term

    parity_sum = sum(sectors, np.zeros_like(off_range_owner))

    maximum_fixed_filter_error = 0.0
    maximum_all_even_slope_error = 0.0
    minimum_all_even_slope = float("inf")
    for index in range(1, path_length):
        reflected = path_length - index
        f_value = PROOF_295.kernel_value(1.0, path_length, index)
        f_reflected = PROOF_295.kernel_value(
            1.0, path_length, reflected
        )
        f_derivative = PROOF_295.kernel_derivative(
            1.0, path_length, index
        )
        f_reflected_derivative = PROOF_295.kernel_derivative(
            1.0, path_length, reflected
        )

        left_plus_value = 1.0 - 0.5 * (f_value + f_reflected)
        left_minus_value = 0.5 * (f_reflected - f_value)
        left_plus_derivative = -0.5 * (
            f_derivative + f_reflected_derivative
        )
        left_minus_derivative = 0.5 * (
            f_reflected_derivative - f_derivative
        )
        expected_left_minus_derivative = 0.5 * (
            path_length - 2 * index
        )

        right_minus_value = 0.5 * (1.0 - 1.0)
        right_minus_derivative = 0.5 * (
            index - reflected
        )
        expected_right_minus_derivative = 0.5 * (
            2 * index - path_length
        )

        maximum_fixed_filter_error = max(
            maximum_fixed_filter_error,
            abs(left_plus_value),
            abs(left_minus_value),
            abs(right_minus_value),
            abs(left_minus_derivative - expected_left_minus_derivative),
            abs(right_minus_derivative - expected_right_minus_derivative),
        )
        maximum_all_even_slope_error = max(
            maximum_all_even_slope_error,
            abs(left_plus_derivative - path_length / 2.0),
        )
        minimum_all_even_slope = min(
            minimum_all_even_slope, abs(left_plus_derivative)
        )

    fixed_observable = np.eye(state["observable"].shape[0], dtype=complex)
    fixed_commutator = commutator(
        fixed_observable, state["path_projection"]
    )

    complete_norm = float(np.linalg.norm(off_range_owner, ord="fro"))
    sector_norm_sum = sum(
        float(np.linalg.norm(sector, ord="fro")) for sector in sectors
    )
    boundary_norm = float(np.linalg.norm(boundary_owner, ord="fro"))

    return {
        "null-coframe block formula error": relative_error(
            null_coframe, expected_null_coframe
        ),
        "off-range block-sum error": relative_error(
            direct_block_sum, off_range_owner
        ),
        "interior-boundary split error": relative_error(
            interior_owner + boundary_owner, off_range_owner
        ),
        "maximum parity-orbit identity error": maximum_parity_orbit_error,
        "weighted interior parity-sum error": relative_error(
            parity_sum, interior_owner
        ),
        "weighted total parity-plus-boundary error": relative_error(
            parity_sum + boundary_owner, off_range_owner
        ),
        "maximum left parity-filter error": maximum_left_filter_error,
        "maximum right parity-filter error": maximum_right_filter_error,
        "maximum commutator parity-filter error": (
            maximum_commutator_filter_error
        ),
        "fixed-mode parity-filter error": maximum_fixed_filter_error,
        "all-even slope formula error": maximum_all_even_slope_error,
        "minimum all-even fixed-mode slope": minimum_all_even_slope,
        "fixed-mode path-commutator error": float(
            np.linalg.norm(fixed_commutator)
        ),
        "complete off-range Frobenius norm": complete_norm,
        "all-even sector Frobenius norm": float(
            np.linalg.norm(sectors[0], ord="fro")
        ),
        "plus-minus-minus sector Frobenius norm": float(
            np.linalg.norm(sectors[1], ord="fro")
        ),
        "minus-plus-minus sector Frobenius norm": float(
            np.linalg.norm(sectors[2], ord="fro")
        ),
        "minus-minus-plus sector Frobenius norm": float(
            np.linalg.norm(sectors[3], ord="fro")
        ),
        "boundary-strip Frobenius norm": boundary_norm,
        "boundary-strip relative magnitude": boundary_norm
        / max(complete_norm, 1e-15),
        "parity-plus-boundary triangle ratio": (
            sector_norm_sum + boundary_norm
        ) / max(complete_norm, 1e-15),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=296)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--single-zero-floor", type=float, default=1.0)
    parser.add_argument("--boundary-floor", type=float, default=0.2)
    args = parser.parse_args()

    checks = certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    print("identity=weighted reflection parity")
    print("status=one hard and three soft interior sectors; source bound open")
    print("checks=BEGIN")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={float(value):.12e}")
    print("checks=END")

    excluded_labels = {
        "minimum all-even fixed-mode slope",
        "complete off-range Frobenius norm",
        "all-even sector Frobenius norm",
        "plus-minus-minus sector Frobenius norm",
        "minus-plus-minus sector Frobenius norm",
        "minus-minus-plus sector Frobenius norm",
        "boundary-strip Frobenius norm",
        "boundary-strip relative magnitude",
        "parity-plus-boundary triangle ratio",
    }
    maximum_exact_error = max(
        float(value)
        for label, value in checks.items()
        if label not in excluded_labels
    )
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "weighted reflection parity certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if checks["minimum all-even fixed-mode slope"] < args.single_zero_floor:
        raise SystemExit("all-even single-zero rejection guard did not fire")
    if checks["boundary-strip relative magnitude"] < args.boundary_floor:
        raise SystemExit("path-boundary retention guard did not fire")

    print("weighted_interior=FOUR_REFLECTION_PARITY_SECTORS")
    print("all_even_sector=SINGLE_FIXED_MODE_ZERO")
    print("other_three_sectors=AT_LEAST_DOUBLE_ZERO")
    print("path_boundary_strip=MANDATORY")
    print("all_weighted_bulk_double_zero=FALSE")
    print("source_outer_sonin_recombination=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
