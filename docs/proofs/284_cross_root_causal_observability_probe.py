#!/usr/bin/env python3
"""Certificate for Proof 284's cross-root causal observability pairing.

Proof 270 assumes a Hermitian detector when it defines the prolate left reward.
For a complex cross detector W=C_xi* C_eta, the correct reward contains W* on
the left-column side.  This script verifies the corrected three-branch
factorization, renewal-column pairing, adjoint symmetry, and polarization.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_270() -> ModuleType:
    path = Path(__file__).with_name(
        "270_renewal_observability_collapse_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_270_for_284", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_270 = load_proof_270()
PROOF_266 = PROOF_270.PROOF_266


def cross_detector(
    multiplicity: int, eta: np.ndarray, xi: np.ndarray
) -> np.ndarray:
    local = np.outer(eta, np.conj(xi))
    return np.kron(np.eye(2, dtype=complex), local)


def owner_data_cross(
    model: dict[str, np.ndarray], detector: np.ndarray
) -> dict[str, np.ndarray]:
    identity = model["identity"]
    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    second_support = model["Q"]
    causal = model["A"]
    band_basis = model["b_basis"]

    survivor = outer @ causal @ band_basis
    outer_escape = complement @ causal @ band_basis
    detector_outer = PROOF_266.commutator(detector, outer)
    detector_second = PROOF_266.commutator(
        detector, second_support
    )

    left_outer = -detector_outer.conj().T @ outer_escape
    left_second = (
        causal
        @ sonin
        @ detector_second.conj().T
        @ (identity - second_support)
        @ band_basis
    )
    left_prolate = (
        causal
        @ sonin
        @ detector.conj().T
        @ second_support
        @ band_basis
    )
    wrong_left_prolate = (
        causal
        @ sonin
        @ detector
        @ second_support
        @ band_basis
    )
    left = left_outer + left_second + left_prolate
    wrong_left = left_outer + left_second + wrong_left_prolate

    gamma = survivor.conj().T @ survivor
    identity_band = np.eye(band_basis.shape[1], dtype=complex)
    delta = identity_band - gamma
    defect = PROOF_270.positive_square_root(delta)
    detector_band = band_basis.conj().T @ detector @ band_basis
    numerator = (
        survivor.conj().T @ detector @ survivor
        - detector_band @ gamma
    )

    return {
        "K": survivor,
        "L_outer": left_outer,
        "L_second": left_second,
        "L_prolate": left_prolate,
        "L": left,
        "wrong_L": wrong_left,
        "Gamma": gamma,
        "Delta": delta,
        "D": defect,
        "N": numerator,
    }


def response_for_detector(
    model: dict[str, np.ndarray], detector: np.ndarray
) -> complex:
    data = owner_data_cross(model, detector)
    return complex(
        np.trace(data["N"] @ np.linalg.inv(data["Gamma"]))
    )


def column_certificate(
    data: dict[str, np.ndarray],
    maximum_power: int,
    tail_tolerance: float,
) -> dict[str, float | complex]:
    survivor = data["K"]
    left = data["L"]
    gamma = data["Gamma"]
    defect = data["D"]
    numerator = data["N"]
    identity = np.eye(gamma.shape[0], dtype=complex)

    complete_response = np.trace(numerator @ np.linalg.inv(gamma))
    right_gram = np.zeros_like(gamma)
    pair_trace = 0.0j
    defect_power = identity.copy()
    for exponent in range(maximum_power + 1):
        right_leg = survivor @ defect_power
        left_leg = left @ defect_power
        right_gram += right_leg.conj().T @ right_leg
        pair_trace += np.trace(left_leg.conj().T @ right_leg)
        defect_power = defect_power @ defect
        if (
            exponent >= 8
            and float(np.linalg.norm(defect_power, ord=2))
            <= tail_tolerance
        ):
            break

    return {
        "complete_response": complex(complete_response),
        "column_response": complex(pair_trace),
        "left_factor_error": PROOF_270.relative_error(
            left.conj().T @ survivor, numerator
        ),
        "wrong_prolate_factor_error": PROOF_270.relative_error(
            data["wrong_L"].conj().T @ survivor, numerator
        ),
        "right_isometry_error": PROOF_270.relative_error(
            right_gram, identity
        ),
        "column_pairing_error": PROOF_270.relative_error(
            pair_trace, complete_response
        ),
        "tail_norm": float(np.linalg.norm(defect_power, ord=2)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=8)
    parser.add_argument("--seed", type=int, default=284)
    parser.add_argument("--maximum-power", type=int, default=10_000)
    parser.add_argument("--tail-tolerance", type=float, default=1e-14)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--wrong-factor-floor", type=float, default=1e-4)
    args = parser.parse_args()

    model = PROOF_266.build_model(args.multiplicity, args.seed)
    rng = np.random.default_rng(args.seed + 17)
    eta = rng.normal(size=args.multiplicity) + 1j * rng.normal(
        size=args.multiplicity
    )
    xi = rng.normal(size=args.multiplicity) + 1j * rng.normal(
        size=args.multiplicity
    )
    eta /= np.linalg.norm(eta)
    xi /= np.linalg.norm(xi)

    detector = cross_detector(args.multiplicity, eta, xi)
    data = owner_data_cross(model, detector)
    checks = column_certificate(
        data, args.maximum_power, args.tail_tolerance
    )

    adjoint_detector = cross_detector(args.multiplicity, xi, eta)
    adjoint_response = response_for_detector(model, adjoint_detector)
    response = complex(checks["complete_response"])
    adjoint_symmetry_error = abs(adjoint_response - np.conj(response)) / max(
        abs(response), 1.0
    )

    polarized_response = 0.0j
    for power in range(4):
        phase = 1j**power
        combined = eta + phase * xi
        diagonal_detector = cross_detector(
            args.multiplicity, combined, combined
        )
        polarized_response += phase * response_for_detector(
            model, diagonal_detector
        ) / 4.0
    polarization_error = abs(polarized_response - response) / max(
        abs(response), 1.0
    )

    print("identity=cross-root causal observability pairing")
    print("status=exact fixed-S complex renewal algebra")
    print(f"multiplicity={args.multiplicity}")
    print(f"complete_response_real={response.real:.12e}")
    print(f"complete_response_imag={response.imag:.12e}")
    print(
        "column_response_real="
        f"{complex(checks['column_response']).real:.12e}"
    )
    print(
        "column_response_imag="
        f"{complex(checks['column_response']).imag:.12e}"
    )
    print(f"left_factor_error={checks['left_factor_error']:.12e}")
    print(
        "wrong_prolate_factor_error="
        f"{checks['wrong_prolate_factor_error']:.12e}"
    )
    print(f"right_isometry_error={checks['right_isometry_error']:.12e}")
    print(f"column_pairing_error={checks['column_pairing_error']:.12e}")
    print(f"adjoint_symmetry_error={adjoint_symmetry_error:.12e}")
    print(f"polarization_error={polarization_error:.12e}")
    print(f"tail_norm={checks['tail_norm']:.12e}")

    exact_errors = (
        float(checks["left_factor_error"]),
        float(checks["right_isometry_error"]),
        float(checks["column_pairing_error"]),
        float(adjoint_symmetry_error),
        float(polarization_error),
    )
    maximum_error = max(exact_errors)
    print(f"maximum_exact_error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"cross-root causal certificate failed: {maximum_error:.6e}"
        )
    if float(checks["wrong_prolate_factor_error"]) < args.wrong_factor_floor:
        raise SystemExit("Hermitian-only prolate reward unexpectedly survived")

    print("cross_root_three_branch_factorization=EXACT")
    print("corrected_prolate_left_reward=USES_W_ADJOINT")
    print("hermitian_only_prolate_reward=REJECTED")
    print("right_survivor_column=ISOMETRY")
    print("cross_root_causal_column_pairing=EXACT")
    print("complex_polarization=EXACT")
    print("stopped_cross_root_scalar_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
