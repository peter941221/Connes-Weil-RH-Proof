#!/usr/bin/env python3
"""Certificate for Proof 292's causal two-boundary generator."""

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


PROOF_291 = load_probe(
    "291_single_generator_path_defect_probe.py",
    "proof_291_for_292",
)
PROOF_285 = PROOF_291.PROOF_285
PROOF_266 = PROOF_291.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> dict[str, float]:
    if horizon < 1:
        raise ValueError("horizon must be positive")

    model = PROOF_266.build_model(multiplicity, seed)
    detector, support_mask = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 47
    )

    identity = model["identity"]
    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    band = model["B"]
    second_support = model["Q"]
    prolate = model["K_prol"]
    causal = model["A"]
    band_basis = model["b_basis"]

    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    killed = outer @ causal @ band_basis
    gamma = killed.conj().T @ killed
    delta = identity_band - gamma
    detector_band = band_basis.conj().T @ detector @ band_basis

    detector_outer = commutator(detector, outer)
    detector_sonin = commutator(detector, sonin)
    detector_second = commutator(detector, second_support)
    detector_prolate = commutator(detector, prolate)

    right_defect = detector @ killed - killed @ detector_band
    left_defect = (
        killed.conj().T @ detector
        - detector_band @ killed.conj().T
    )

    outer_boundary = detector_outer @ causal @ band_basis
    returned_outer = (
        outer
        @ causal
        @ complement
        @ detector_outer
        @ band_basis
    )
    sonin_boundary = (
        -outer
        @ causal
        @ sonin
        @ detector_sonin
        @ band_basis
    )
    two_boundary_generator = outer_boundary + sonin_boundary
    three_branch_generator = (
        outer_boundary + returned_outer + sonin_boundary
    )

    left_two_boundary = (
        -band_basis.conj().T
        @ causal.conj().T
        @ detector_outer
        +band_basis.conj().T
        @ detector_sonin
        @ sonin
        @ causal.conj().T
        @ outer
    )

    reconstructed_sonin = (
        outer @ second_support @ outer - prolate
    )
    expanded_sonin_commutator = (
        detector_outer @ second_support @ outer
        + outer @ detector_second @ outer
        + outer @ second_support @ detector_outer
        - detector_prolate
    )

    maximum_collapsed_path_error = 0.0
    for exponent in range(horizon + 1):
        delta_power = np.linalg.matrix_power(delta, exponent)
        direct_block = (
            detector @ killed @ delta_power
            - killed @ delta_power @ detector_band
        )
        power_commutator = PROOF_291.commutator_power(
            detector_band, delta, exponent
        )
        collapsed_block = (
            two_boundary_generator @ delta_power
            + killed @ power_commutator
        )
        maximum_collapsed_path_error = max(
            maximum_collapsed_path_error,
            relative_error(direct_block, collapsed_block),
        )

    tail_exponent = horizon + 1
    direct_tail = commutator(
        detector_band, np.linalg.matrix_power(delta, tail_exponent)
    )
    generated_tail = PROOF_291.commutator_power(
        detector_band, delta, tail_exponent
    )

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
    fixed_left = (
        killed.conj().T @ identity
        - identity_band @ killed.conj().T
    )

    complete_norm = float(np.linalg.norm(right_defect, ord="fro"))
    two_boundary_norm_sum = sum(
        float(np.linalg.norm(branch, ord="fro"))
        for branch in (outer_boundary, sonin_boundary)
    )

    return {
        "causal EAC deletion error": float(
            np.linalg.norm(outer @ causal @ complement)
        ),
        "dual CA-star-E deletion error": float(
            np.linalg.norm(
                complement @ causal.conj().T @ outer
            )
        ),
        "detector-causal commutator error": float(
            np.linalg.norm(commutator(detector, causal))
        ),
        "detector-adjoint-causal commutator error": float(
            np.linalg.norm(commutator(detector, causal.conj().T))
        ),
        "Sonin reconstruction error": relative_error(
            sonin, reconstructed_sonin
        ),
        "complete Sonin commutator decomposition error": relative_error(
            detector_sonin, expanded_sonin_commutator
        ),
        "former returned-outer branch norm": float(
            np.linalg.norm(returned_outer)
        ),
        "three-to-two boundary collapse error": relative_error(
            three_branch_generator, two_boundary_generator
        ),
        "direct two-boundary generator error": relative_error(
            right_defect, two_boundary_generator
        ),
        "left two-boundary generator error": relative_error(
            left_defect, left_two_boundary
        ),
        "maximum collapsed path-block error": (
            maximum_collapsed_path_error
        ),
        "collapsed survivor-tail error": relative_error(
            direct_tail, generated_tail
        ),
        "diagonal left-versus-adjoint error": relative_error(
            hermitian_left, hermitian_right.conj().T
        ),
        "outer crossing off-support error": float(
            np.linalg.norm(detector_outer * (1.0 - support_mask))
        ),
        "fixed-mode right-defect error": float(np.linalg.norm(fixed_right)),
        "fixed-mode left-defect error": float(np.linalg.norm(fixed_left)),
        "two-boundary triangle ratio": two_boundary_norm_sum
        / max(complete_norm, 1e-15),
        "complete generator Frobenius norm": complete_norm,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=292)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    checks = certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    print("identity=causal two-boundary path generator")
    print("status=returned outer branch deleted; stopped bound open")
    print("checks=BEGIN")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={float(value):.12e}")
    print("checks=END")

    exact_labels = (
        "causal EAC deletion error",
        "dual CA-star-E deletion error",
        "detector-causal commutator error",
        "detector-adjoint-causal commutator error",
        "Sonin reconstruction error",
        "complete Sonin commutator decomposition error",
        "former returned-outer branch norm",
        "three-to-two boundary collapse error",
        "direct two-boundary generator error",
        "left two-boundary generator error",
        "maximum collapsed path-block error",
        "collapsed survivor-tail error",
        "diagonal left-versus-adjoint error",
        "outer crossing off-support error",
        "fixed-mode right-defect error",
        "fixed-mode left-defect error",
    )
    maximum_exact_error = max(float(checks[label]) for label in exact_labels)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "causal two-boundary certificate failed: "
            f"{maximum_exact_error:.6e}"
        )

    print("returned_outer_branch=EXACTLY_ZERO")
    print("physical_generator=OUTER_MINUS_SONIN_BOUNDARY")
    print("sonin_subbranches_estimated_separately=FALSE")
    print("detector_support_growth=NONE_FROM_COLLAPSE")
    print("stopped_path_transform_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
