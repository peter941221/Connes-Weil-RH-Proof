#!/usr/bin/env python3
"""Certificate for Proof 285's support-first boundary renewal functional.

For a cross-root convolution detector commuting with the causal Euler inverse,
the three physical numerator branches can be recombined before the renewal.
After cycling only completed fixed-S products, the detector sits outside one
signed outer-minus-Sonin boundary kernel.  Its finite support then clips that
kernel before the renewal powers are expanded.

The boundary kernel is not the endpoint projection difference as an operator.
The identity is a trace-functional identity on the convolution commutant.  A
noncommuting detector guard rejects the stronger statement.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_284() -> ModuleType:
    path = Path(__file__).with_name(
        "284_cross_root_causal_observability_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_284_for_285", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_284 = load_proof_284()
PROOF_266 = PROOF_284.PROOF_266
PROOF_270 = PROOF_284.PROOF_270


def zero_extension_convolution(
    root: np.ndarray, size: int
) -> np.ndarray:
    if root.ndim != 1 or root.size % 2 != 1:
        raise ValueError("root must have odd one-dimensional support")
    radius = root.size // 2
    operator = np.zeros((size, size), dtype=complex)
    for row in range(size):
        for column in range(size):
            root_index = row - column + radius
            if 0 <= root_index < root.size:
                operator[row, column] = root[root_index]
    return operator


def support_mask(
    multiplicity: int, displacement_radius: int
) -> np.ndarray:
    mask = np.zeros((2 * multiplicity, 2 * multiplicity), dtype=float)
    for block in range(2):
        start = block * multiplicity
        for row in range(multiplicity):
            for column in range(multiplicity):
                if abs(row - column) <= displacement_radius:
                    mask[start + row, start + column] = 1.0
    return mask


def structured_cross_detector(
    multiplicity: int, root_radius: int, seed: int
) -> tuple[np.ndarray, np.ndarray]:
    if root_radius < 1 or 2 * root_radius + 1 > multiplicity:
        raise ValueError("root support does not fit the multiplicity")
    rng = np.random.default_rng(seed)
    root_size = 2 * root_radius + 1
    eta = rng.normal(size=root_size) + 1j * rng.normal(size=root_size)
    xi = rng.normal(size=root_size) + 1j * rng.normal(size=root_size)
    eta /= np.linalg.norm(eta)
    xi /= np.linalg.norm(xi)
    convolution_eta = zero_extension_convolution(eta, multiplicity)
    convolution_xi = zero_extension_convolution(xi, multiplicity)
    local_detector = convolution_xi.conj().T @ convolution_eta
    detector = np.kron(np.eye(2, dtype=complex), local_detector)
    mask = support_mask(multiplicity, 2 * root_radius)
    return detector, mask


def certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    maximum_power: int,
    tail_tolerance: float,
) -> dict[str, float | complex]:
    model = PROOF_266.build_model(multiplicity, seed)
    detector, mask = structured_cross_detector(
        multiplicity, root_radius, seed + 31
    )

    identity = model["identity"]
    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    band = model["B"]
    second_support = model["Q"]
    causal = model["A"]
    band_basis = model["b_basis"]

    survivor = outer @ causal @ band_basis
    gamma = survivor.conj().T @ survivor
    inverse_gamma = np.linalg.inv(gamma)
    identity_band = np.eye(gamma.shape[0], dtype=complex)
    delta = identity_band - gamma

    detector_band = band_basis.conj().T @ detector @ band_basis
    numerator = (
        survivor.conj().T @ detector @ survivor
        - detector_band @ gamma
    )
    detector_outer = PROOF_266.commutator(detector, outer)
    detector_sonin = PROOF_266.commutator(detector, sonin)
    detector_second = PROOF_266.commutator(detector, second_support)

    outer_branch = (
        -band_basis.conj().T
        @ causal.conj().T
        @ complement
        @ detector_outer
        @ outer
        @ causal
        @ band_basis
    )
    sonin_branch = (
        band_basis.conj().T
        @ detector_sonin
        @ sonin
        @ causal.conj().T
        @ survivor
    )
    second_branch = (
        band_basis.conj().T
        @ (identity - second_support)
        @ detector_second
        @ sonin
        @ causal.conj().T
        @ survivor
    )
    prolate_branch = (
        band_basis.conj().T
        @ second_support
        @ detector
        @ sonin
        @ causal.conj().T
        @ survivor
    )
    collapsed_numerator = (
        -band_basis.conj().T
        @ causal.conj().T
        @ complement
        @ detector
        @ survivor
        + band_basis.conj().T
        @ detector
        @ sonin
        @ causal.conj().T
        @ survivor
    )

    endpoint_difference = (
        survivor @ inverse_gamma @ survivor.conj().T - band
    )
    boundary_kernel = (
        sonin
        @ causal.conj().T
        @ survivor
        @ inverse_gamma
        @ band_basis.conj().T
        - survivor
        @ inverse_gamma
        @ band_basis.conj().T
        @ causal.conj().T
        @ complement
    )
    clipped_boundary = boundary_kernel * mask

    endpoint_response = np.trace(numerator @ inverse_gamma)
    projection_response = np.trace(detector @ endpoint_difference)
    boundary_response = np.trace(detector @ boundary_kernel)
    clipped_response = np.trace(detector @ clipped_boundary)

    renewal_response = 0.0j
    maximum_term_clip_error = 0.0
    absolute_renewal_mass = 0.0
    absolute_boundary_mass = 0.0
    power = identity_band.copy()
    terminal_power_norm = 1.0
    for exponent in range(maximum_power + 1):
        sonin_term = (
            sonin
            @ causal.conj().T
            @ survivor
            @ power
            @ band_basis.conj().T
        )
        outer_term = (
            -survivor
            @ power
            @ band_basis.conj().T
            @ causal.conj().T
            @ complement
        )
        boundary_term = sonin_term + outer_term
        term_response = np.trace(detector @ boundary_term)
        sonin_response = np.trace(detector @ sonin_term)
        outer_response = np.trace(detector @ outer_term)
        clipped_term_response = np.trace(
            detector @ (boundary_term * mask)
        )
        renewal_response += term_response
        absolute_renewal_mass += abs(term_response)
        absolute_boundary_mass += abs(sonin_response) + abs(outer_response)
        maximum_term_clip_error = max(
            maximum_term_clip_error,
            abs(term_response - clipped_term_response),
        )
        power = power @ delta
        terminal_power_norm = float(np.linalg.norm(power, ord=2))
        if exponent >= 8 and terminal_power_norm <= tail_tolerance:
            break

    rng = np.random.default_rng(seed + 97)
    noncommuting_detector = rng.normal(size=identity.shape) + 1j * rng.normal(
        size=identity.shape
    )
    noncommuting_detector /= np.linalg.norm(
        noncommuting_detector, ord=2
    )
    noncommuting_endpoint = np.trace(
        noncommuting_detector @ endpoint_difference
    )
    noncommuting_boundary = np.trace(
        noncommuting_detector @ boundary_kernel
    )

    adjoint_response = np.trace(detector.conj().T @ boundary_kernel)
    return {
        "detector causal commutator": PROOF_270.relative_error(
            detector @ causal - causal @ detector, 0.0
        ),
        "detector causal-adjoint commutator": PROOF_270.relative_error(
            detector @ causal.conj().T
            - causal.conj().T @ detector,
            0.0,
        ),
        "cross detector non-Hermitian gap": float(
            np.linalg.norm(detector - detector.conj().T, ord=2)
        ),
        "detector support leakage": PROOF_270.relative_error(
            detector * (1.0 - mask), 0.0
        ),
        "outer plus Sonin numerator error": PROOF_270.relative_error(
            outer_branch + sonin_branch, numerator
        ),
        "second plus prolate error": PROOF_270.relative_error(
            second_branch + prolate_branch, sonin_branch
        ),
        "collapsed numerator error": PROOF_270.relative_error(
            collapsed_numerator, numerator
        ),
        "endpoint projection response error": PROOF_270.relative_error(
            projection_response, endpoint_response
        ),
        "boundary functional response error": PROOF_270.relative_error(
            boundary_response, endpoint_response
        ),
        "support-clipped response error": PROOF_270.relative_error(
            clipped_response, endpoint_response
        ),
        "renewal response error": PROOF_270.relative_error(
            renewal_response, endpoint_response
        ),
        "maximum renewal-term clip error": maximum_term_clip_error,
        "adjoint symmetry error": PROOF_270.relative_error(
            adjoint_response, np.conj(endpoint_response)
        ),
        "boundary kernel operator gap": PROOF_270.relative_error(
            boundary_kernel, endpoint_difference
        ),
        "discarded kernel Frobenius mass": float(
            np.linalg.norm(boundary_kernel - clipped_boundary, ord="fro")
        ),
        "noncommuting detector commutator": float(
            np.linalg.norm(
                noncommuting_detector @ causal
                - causal @ noncommuting_detector,
                ord=2,
            )
        ),
        "noncommuting trace-functional gap": float(
            abs(noncommuting_endpoint - noncommuting_boundary)
        ),
        "absolute renewal cancellation ratio": float(
            absolute_renewal_mass / max(abs(endpoint_response), 1e-15)
        ),
        "absolute boundary cancellation ratio": float(
            absolute_boundary_mass / max(abs(endpoint_response), 1e-15)
        ),
        "terminal renewal-power norm": terminal_power_norm,
        "endpoint response": complex(endpoint_response),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=285)
    parser.add_argument("--maximum-power", type=int, default=10_000)
    parser.add_argument("--tail-tolerance", type=float, default=1e-14)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--guard-floor", type=float, default=1e-4)
    args = parser.parse_args()

    checks = certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.maximum_power,
        args.tail_tolerance,
    )
    response = complex(checks["endpoint response"])
    print("identity=support-first two-boundary renewal functional")
    print("status=exact fixed-S convolution-commutant trace algebra")
    print(f"multiplicity={args.multiplicity}")
    print(f"root_radius={args.root_radius}")
    print(f"endpoint_response_real={response.real:.12e}")
    print(f"endpoint_response_imag={response.imag:.12e}")
    for label, value in checks.items():
        if label == "endpoint response":
            continue
        print(f"{label.replace(' ', '_')}={float(value):.12e}")

    exact_labels = (
        "detector causal commutator",
        "detector causal-adjoint commutator",
        "detector support leakage",
        "outer plus Sonin numerator error",
        "second plus prolate error",
        "collapsed numerator error",
        "endpoint projection response error",
        "boundary functional response error",
        "support-clipped response error",
        "renewal response error",
        "maximum renewal-term clip error",
        "adjoint symmetry error",
    )
    maximum_exact_error = max(float(checks[label]) for label in exact_labels)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "support-first boundary certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    guard_labels = (
        "cross detector non-Hermitian gap",
        "boundary kernel operator gap",
        "discarded kernel Frobenius mass",
        "noncommuting detector commutator",
        "noncommuting trace-functional gap",
    )
    if min(float(checks[label]) for label in guard_labels) < args.guard_floor:
        raise SystemExit("a rejection guard unexpectedly collapsed")

    print("three_branch_to_two_boundary_recombination=EXACT")
    print("detector_extraction_on_convolution_commutant=EXACT")
    print("compact_support_before_renewal_expansion=EXACT")
    print("boundary_kernel_operator_identity=FALSE")
    print("noncommuting_detector_extension=REJECTED")
    print("positive_kernel_norm_estimate=REJECTED")
    print("first_missing_prime_scalar_disintegration=OPEN")
    print("complete_signed_extra_half_power=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
