#!/usr/bin/env python3
"""Certificate for Proof 291's single-generator path defect reduction."""

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
    "proof_286_for_291",
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


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def commutator_power(
    detector_band: np.ndarray, delta: np.ndarray, exponent: int
) -> np.ndarray:
    if exponent == 0:
        return np.zeros_like(delta)
    base = commutator(detector_band, delta)
    return sum(
        (
            np.linalg.matrix_power(delta, left_power)
            @ base
            @ np.linalg.matrix_power(
                delta, exponent - 1 - left_power
            )
            for left_power in range(exponent)
        ),
        np.zeros_like(delta),
    )


def certificate(
    multiplicity: int, root_radius: int, seed: int, horizon: int
) -> dict[str, float]:
    if horizon < 1:
        raise ValueError("horizon must be positive")
    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 43
    )

    identity = model["identity"]
    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    band = model["B"]
    causal = model["A"]
    band_basis = model["b_basis"]
    killed = outer @ causal @ band_basis
    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    gamma = killed.conj().T @ killed
    delta = identity_band - gamma
    detector_band = band_basis.conj().T @ detector @ band_basis

    right_defect = detector @ killed - killed @ detector_band
    left_defect = (
        killed.conj().T @ detector
        - detector_band @ killed.conj().T
    )
    direct_delta_commutator = commutator(detector_band, delta)
    generated_delta_commutator = (
        left_defect @ killed - killed.conj().T @ right_defect
    )

    maximum_power_rule_error = 0.0
    maximum_emission_error = 0.0
    direct_blocks: list[np.ndarray] = []
    generated_blocks: list[np.ndarray] = []
    for exponent in range(horizon + 1):
        delta_power = np.linalg.matrix_power(delta, exponent)
        direct_block = (
            detector @ killed @ delta_power
            - killed @ delta_power @ detector_band
        )
        direct_blocks.append(direct_block)
        power_commutator = commutator_power(
            detector_band, delta, exponent
        )
        maximum_power_rule_error = max(
            maximum_power_rule_error,
            relative_error(
                power_commutator,
                commutator(detector_band, delta_power),
            ),
        )
        generated_block = right_defect @ delta_power + killed @ power_commutator
        generated_blocks.append(generated_block)
        maximum_emission_error = max(
            maximum_emission_error,
            relative_error(direct_block, generated_block),
        )

    tail_exponent = horizon + 1
    direct_tail = commutator(
        detector_band, np.linalg.matrix_power(delta, tail_exponent)
    )
    generated_tail = commutator_power(
        detector_band, delta, tail_exponent
    )
    direct_path_defect = np.vstack(direct_blocks + [direct_tail])
    generated_path_defect = np.vstack(generated_blocks + [generated_tail])

    physical_outer = commutator(detector, outer) @ causal @ band_basis
    returned_outer = (
        outer
        @ causal
        @ complement
        @ commutator(detector, outer)
        @ band_basis
    )
    complete_sonin = (
        -outer
        @ causal
        @ sonin
        @ commutator(detector, sonin)
        @ band_basis
    )
    physical_generator = physical_outer + returned_outer + complete_sonin
    branch_norm_sum = sum(
        float(np.linalg.norm(branch, ord="fro"))
        for branch in (physical_outer, returned_outer, complete_sonin)
    )
    complete_norm = float(np.linalg.norm(right_defect, ord="fro"))

    hermitian_detector = 0.5 * (detector + detector.conj().T)
    hermitian_band = (
        band_basis.conj().T @ hermitian_detector @ band_basis
    )
    hermitian_right = (
        hermitian_detector @ killed - killed @ hermitian_band
    )
    hermitian_left = (
        killed.conj().T @ hermitian_detector
        - hermitian_band @ killed.conj().T
    )

    fixed_right = identity @ killed - killed @ identity_band
    fixed_left = killed.conj().T @ identity - identity_band @ killed.conj().T

    return {
        "Delta commutator generation error": relative_error(
            direct_delta_commutator, generated_delta_commutator
        ),
        "maximum commutator power-rule error": maximum_power_rule_error,
        "maximum generated emission-block error": maximum_emission_error,
        "generated survivor-tail error": relative_error(
            direct_tail, generated_tail
        ),
        "complete generated path-defect error": relative_error(
            direct_path_defect, generated_path_defect
        ),
        "physical three-crossing generator error": relative_error(
            right_defect, physical_generator
        ),
        "diagonal left-versus-adjoint error": relative_error(
            hermitian_left, hermitian_right.conj().T
        ),
        "fixed-mode right-defect error": float(np.linalg.norm(fixed_right)),
        "fixed-mode left-defect error": float(np.linalg.norm(fixed_left)),
        "generator branch-norm triangle ratio": branch_norm_sum
        / max(complete_norm, 1e-15),
        "complete generator Frobenius norm": complete_norm,
        "complete path-defect Frobenius norm": float(
            np.linalg.norm(direct_path_defect, ord="fro")
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=291)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    checks = certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    print("identity=single-generator renewal path defect")
    print("status=all path detector defects generated; stopped bound open")
    print("checks=BEGIN")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={float(value):.12e}")
    print("checks=END")

    exact_labels = (
        "Delta commutator generation error",
        "maximum commutator power-rule error",
        "maximum generated emission-block error",
        "generated survivor-tail error",
        "complete generated path-defect error",
        "physical three-crossing generator error",
        "diagonal left-versus-adjoint error",
        "fixed-mode right-defect error",
        "fixed-mode left-defect error",
    )
    maximum_exact_error = max(float(checks[label]) for label in exact_labels)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "single-generator path-defect certificate failed: "
            f"{maximum_exact_error:.6e}"
        )

    print("path_detector_defect=SINGLE_GENERATOR_AND_LEFT_COMPANION")
    print("diagonal_path_detector_defect=SINGLE_GENERATOR_AND_ADJOINT")
    print("detector_support_growth=NONE_FROM_HORIZON")
    print("branchwise_generator_norm_used=FALSE")
    print("stopped_path_transform_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
