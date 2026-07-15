#!/usr/bin/env python3
"""Certificate for Proof 293's observable two-boundary path compression."""

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


PROOF_292 = load_probe(
    "292_causal_two_boundary_generator_probe.py",
    "proof_292_for_293",
)
PROOF_285 = PROOF_292.PROOF_285
PROOF_266 = PROOF_292.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


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


def certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> dict[str, float]:
    if horizon < 1:
        raise ValueError("horizon must be positive")

    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 53
    )

    identity = model["identity"]
    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    causal = model["A"]
    band_basis = model["b_basis"]

    killed = outer @ causal @ band_basis
    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    gamma = killed.conj().T @ killed
    delta = identity_band - gamma
    delta = 0.5 * (delta + delta.conj().T)
    detector_band = band_basis.conj().T @ detector @ band_basis

    right_defect = detector @ killed - killed @ detector_band
    left_defect = (
        killed.conj().T @ detector
        - detector_band @ killed.conj().T
    )
    visible_generator = outer @ right_defect
    escaping_generator = complement @ right_defect
    visible_left = left_defect @ outer

    detector_sonin = commutator(detector, sonin)
    physical_visible = (
        -outer
        @ detector
        @ complement
        @ causal
        @ band_basis
        -outer
        @ causal
        @ sonin
        @ detector_sonin
        @ band_basis
    )
    physical_visible_left = (
        -band_basis.conj().T
        @ causal.conj().T
        @ complement
        @ detector
        @ outer
        +band_basis.conj().T
        @ detector_sonin
        @ sonin
        @ causal.conj().T
        @ outer
    )
    centered_numerator = (
        killed.conj().T @ detector @ killed
        - detector_band @ gamma
    )
    support_first_numerator = (
        -band_basis.conj().T
        @ causal.conj().T
        @ complement
        @ detector
        @ killed
        +band_basis.conj().T
        @ detector
        @ sonin
        @ causal.conj().T
        @ killed
    )

    right_blocks = [
        killed @ np.linalg.matrix_power(delta, exponent)
        for exponent in range(horizon + 1)
    ]
    right_blocks.append(np.linalg.matrix_power(delta, horizon + 1))
    right_path = np.vstack(right_blocks)

    left_blocks = [killed for _ in range(horizon + 1)]
    left_blocks.append(identity_band)
    left_path = np.vstack(left_blocks)

    observable = block_diagonal(
        [detector for _ in range(horizon + 1)]
        + [detector_band]
    )
    compressed_detector = outer @ detector @ outer
    compressed_observable = block_diagonal(
        [compressed_detector for _ in range(horizon + 1)]
        + [detector_band]
    )

    original_intertwinement = (
        observable @ right_path - right_path @ detector_band
    )
    visible_intertwinement = (
        compressed_observable @ right_path
        - right_path @ detector_band
    )
    escape_blocks = [
        escaping_generator @ np.linalg.matrix_power(delta, exponent)
        for exponent in range(horizon + 1)
    ]
    escape_blocks.append(np.zeros_like(identity_band))
    escape_path = np.vstack(escape_blocks)

    visible_delta_commutator = (
        visible_left @ killed
        - killed.conj().T @ visible_generator
    )
    direct_delta_commutator = commutator(detector_band, delta)

    generated_visible_blocks: list[np.ndarray] = []
    for exponent in range(horizon + 1):
        delta_power = np.linalg.matrix_power(delta, exponent)
        power_commutator = sum(
            (
                np.linalg.matrix_power(delta, left_power)
                @ visible_delta_commutator
                @ np.linalg.matrix_power(
                    delta, exponent - 1 - left_power
                )
                for left_power in range(exponent)
            ),
            np.zeros_like(delta),
        )
        generated_visible_blocks.append(
            visible_generator @ delta_power
            + killed @ power_commutator
        )
    tail_exponent = horizon + 1
    generated_tail = sum(
        (
            np.linalg.matrix_power(delta, left_power)
            @ visible_delta_commutator
            @ np.linalg.matrix_power(
                delta, tail_exponent - 1 - left_power
            )
            for left_power in range(tail_exponent)
        ),
        np.zeros_like(delta),
    )
    generated_visible_path = np.vstack(
        generated_visible_blocks + [generated_tail]
    )

    right_gram = right_path.conj().T @ right_path
    canonical_dual = right_path @ np.linalg.inv(right_gram)
    path_projection = canonical_dual @ right_path.conj().T
    path_identity = np.eye(path_projection.shape[0], dtype=complex)

    original_response = (
        left_path.conj().T @ observable @ right_path
        - detector_band
    )
    compressed_response = (
        left_path.conj().T @ compressed_observable @ right_path
        - detector_band
    )
    original_split = (
        canonical_dual.conj().T @ original_intertwinement
        + left_path.conj().T
        @ (path_identity - path_projection)
        @ original_intertwinement
    )
    visible_split = (
        canonical_dual.conj().T @ visible_intertwinement
        + left_path.conj().T
        @ (path_identity - path_projection)
        @ visible_intertwinement
    )

    hermitian_detector = 0.5 * (detector + detector.conj().T)
    hermitian_band = (
        band_basis.conj().T @ hermitian_detector @ band_basis
    )
    hermitian_right = outer @ (
        hermitian_detector @ killed - killed @ hermitian_band
    )
    hermitian_left = (
        killed.conj().T @ hermitian_detector
        - hermitian_band @ killed.conj().T
    ) @ outer

    fixed_visible = outer @ (
        identity @ killed - killed @ identity_band
    )
    fixed_left = (
        killed.conj().T @ identity
        - identity_band @ killed.conj().T
    ) @ outer

    outer_return = (
        -outer
        @ detector
        @ complement
        @ causal
        @ band_basis
    )
    sonin_return = (
        -outer
        @ causal
        @ sonin
        @ detector_sonin
        @ band_basis
    )
    branch_norm_sum = sum(
        float(np.linalg.norm(branch, ord="fro"))
        for branch in (outer_return, sonin_return)
    )
    visible_norm = float(np.linalg.norm(visible_generator, ord="fro"))

    return {
        "escaping generator formula error": relative_error(
            escaping_generator, complement @ detector @ killed
        ),
        "generator visible-plus-escape error": relative_error(
            right_defect, visible_generator + escaping_generator
        ),
        "physical visible generator error": relative_error(
            visible_generator, physical_visible
        ),
        "physical visible left-generator error": relative_error(
            visible_left, physical_visible_left
        ),
        "visible-left numerator readback error": relative_error(
            visible_left @ killed, centered_numerator
        ),
        "support-first numerator alignment error": relative_error(
            visible_left @ killed, support_first_numerator
        ),
        "visible Delta commutator error": relative_error(
            direct_delta_commutator, visible_delta_commutator
        ),
        "original-versus-compressed path-response error": relative_error(
            original_response, compressed_response
        ),
        "path defect visible-plus-escape error": relative_error(
            original_intertwinement,
            visible_intertwinement + escape_path,
        ),
        "generated visible path-defect error": relative_error(
            visible_intertwinement, generated_visible_path
        ),
        "right-frame escape orthogonality error": float(
            np.linalg.norm(right_path.conj().T @ escape_path)
        ),
        "left-frame escape orthogonality error": float(
            np.linalg.norm(left_path.conj().T @ escape_path)
        ),
        "path-projection escape error": float(
            np.linalg.norm(path_projection @ escape_path)
        ),
        "canonical-dual escape contribution error": float(
            np.linalg.norm(canonical_dual.conj().T @ escape_path)
        ),
        "off-range escape contribution error": float(
            np.linalg.norm(
                left_path.conj().T
                @ (path_identity - path_projection)
                @ escape_path
            )
        ),
        "original-versus-visible canonical-split error": relative_error(
            original_split, visible_split
        ),
        "visible split versus ordered-response error": relative_error(
            visible_split, original_response
        ),
        "diagonal visible-left versus adjoint error": relative_error(
            hermitian_left, hermitian_right.conj().T
        ),
        "fixed-mode visible-generator error": float(
            np.linalg.norm(fixed_visible)
        ),
        "fixed-mode visible-left error": float(np.linalg.norm(fixed_left)),
        "visible two-boundary triangle ratio": branch_norm_sum
        / max(visible_norm, 1e-15),
        "escaping generator Frobenius norm": float(
            np.linalg.norm(escaping_generator, ord="fro")
        ),
        "visible generator Frobenius norm": visible_norm,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=293)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    checks = certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    print("identity=observable two-boundary finite path")
    print("status=one-way escape deleted; visible stopped bound open")
    print("checks=BEGIN")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={float(value):.12e}")
    print("checks=END")

    exact_labels = tuple(
        label for label in checks if not label.endswith("Frobenius norm")
        and label != "visible two-boundary triangle ratio"
    )
    maximum_exact_error = max(float(checks[label]) for label in exact_labels)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "observable two-boundary path certificate failed: "
            f"{maximum_exact_error:.6e}"
        )

    print("emission_observable=EWE")
    print("one_way_C_escape=PATH_INVISIBLE")
    print("ordered_Gram_anomaly=RETAINED")
    print("physical_generator=OUTER_RETURN_MINUS_SONIN")
    print("branchwise_norm_used=FALSE")
    print("visible_stopped_path_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
