#!/usr/bin/env python3
"""Finite audit of the Proof 339 Hankel-owner substitution.

The emission corner of the right-path projection is Hankel, but the actual
weighted off-range owner Z^* [O,P] R is not.  The certificate measures that
failure and the nonzero canonical/boundary contributions.  It does not prove
or disprove the continuous Gate 3U estimate.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_proof_290():
    path = Path(__file__).with_name(
        "290_biorthogonal_finite_horizon_renewal_probe.py"
    )
    specification = importlib.util.spec_from_file_location("proof_290_for_340", path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_290 = load_proof_290()


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def block_diagonal(blocks: list[np.ndarray]) -> np.ndarray:
    rows = sum(block.shape[0] for block in blocks)
    columns = sum(block.shape[1] for block in blocks)
    result = np.zeros((rows, columns), dtype=complex)
    row_offset = 0
    column_offset = 0
    for block in blocks:
        block_rows, block_columns = block.shape
        result[
            row_offset : row_offset + block_rows,
            column_offset : column_offset + block_columns,
        ] = block
        row_offset += block_rows
        column_offset += block_columns
    return result


def certificate(
    multiplicity: int, root_radius: int, seed: int, horizon: int
) -> dict[str, float]:
    model = PROOF_290.PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_290.PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 37
    )
    outer = model["E"]
    causal = model["A"]
    band_basis = model["b_basis"]
    killed = outer @ causal @ band_basis
    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    gamma = killed.conj().T @ killed
    delta = 0.5 * (identity_band - gamma + (identity_band - gamma).conj().T)
    detector_band = band_basis.conj().T @ detector @ band_basis

    emission_blocks = [
        killed @ np.linalg.matrix_power(delta, power)
        for power in range(horizon + 1)
    ]
    tail_block = np.linalg.matrix_power(delta, horizon + 1)
    right_blocks = emission_blocks + [tail_block]
    right_path = np.vstack(right_blocks)
    left_blocks = [killed for _ in range(horizon + 1)] + [identity_band]
    left_path = np.vstack(left_blocks)
    observable = block_diagonal(
        [detector for _ in range(horizon + 1)] + [detector_band]
    )
    right_gram = right_path.conj().T @ right_path
    canonical_dual = right_path @ np.linalg.inv(right_gram)
    projection = canonical_dual @ right_path.conj().T
    null_coframe = left_path - canonical_dual
    intertwinement = observable @ right_path - right_path @ detector_band
    path_commutator = observable @ projection - projection @ observable

    row_sizes = [block.shape[0] for block in right_blocks]
    row_offsets = np.cumsum([0] + row_sizes)

    def block(operator: np.ndarray, row: int, column: int) -> np.ndarray:
        return operator[
            row_offsets[row] : row_offsets[row + 1],
            row_offsets[column] : row_offsets[column + 1],
        ]

    def row_block(operator: np.ndarray, row: int) -> np.ndarray:
        return operator[row_offsets[row] : row_offsets[row + 1], :]

    projection_hankel_error = 0.0
    commutator_hankel_error = 0.0
    weighted_hankel_error = 0.0
    for row in range(1, horizon):
        for column in range(1, horizon):
            projection_hankel_error = max(
                projection_hankel_error,
                relative_error(
                    block(projection, row + 1, column),
                    block(projection, row, column + 1),
                ),
            )
            commutator_hankel_error = max(
                commutator_hankel_error,
                relative_error(
                    block(path_commutator, row + 1, column),
                    block(path_commutator, row, column + 1),
                ),
            )
            weighted_left = (
                row_block(null_coframe, row + 1).conj().T
                @ block(path_commutator, row + 1, column)
                @ right_blocks[column]
            )
            weighted_right = (
                row_block(null_coframe, row).conj().T
                @ block(path_commutator, row, column + 1)
                @ right_blocks[column + 1]
            )
            weighted_hankel_error = max(
                weighted_hankel_error,
                relative_error(weighted_left, weighted_right),
            )

    canonical = canonical_dual.conj().T @ intertwinement
    off_range = null_coframe.conj().T @ path_commutator @ right_path
    full = canonical + off_range

    tail_index = horizon + 1
    boundary = np.zeros_like(full)
    for row in range(horizon + 2):
        for column in range(horizon + 2):
            if row not in (0, tail_index) and column not in (0, tail_index):
                continue
            boundary += (
                row_block(null_coframe, row).conj().T
                @ block(path_commutator, row, column)
                @ right_blocks[column]
            )

    return {
        "projection Hankel error": projection_hankel_error,
        "commutator Hankel error": commutator_hankel_error,
        "weighted owner Hankel mismatch": weighted_hankel_error,
        "canonical response norm": float(np.linalg.norm(canonical)),
        "off-range response norm": float(np.linalg.norm(off_range)),
        "path-boundary norm": float(np.linalg.norm(boundary)),
        "full response norm": float(np.linalg.norm(full)),
        "boundary relative magnitude": float(
            np.linalg.norm(boundary) / max(np.linalg.norm(off_range), 1e-15)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=340)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    args = parser.parse_args()
    checks = certificate(
        args.multiplicity, args.root_radius, args.seed, args.horizon
    )
    print("identity=Hankel-corner versus complete weighted owner audit")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    if checks["projection Hankel error"] > args.tolerance:
        raise RuntimeError("right-path projection lost its Hankel identity")
    if checks["commutator Hankel error"] > args.tolerance:
        raise RuntimeError("emission commutator lost its Hankel identity")
    if checks["weighted owner Hankel mismatch"] <= 1e-5:
        raise RuntimeError("weighted-owner mismatch guard did not separate")
    if min(
        checks["canonical response norm"],
        checks["path-boundary norm"],
        checks["full response norm"],
    ) <= 1e-8:
        raise RuntimeError("hard-package contribution unexpectedly vanished")
    print("emission_hankel_corner=EXACT")
    print("complete_weighted_owner_is_hankel=FALSE")
    print("proof_339_same_object_identification=REJECTED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
