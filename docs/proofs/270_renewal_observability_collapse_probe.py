#!/usr/bin/env python3
"""Certificate for the renewal-to-observability collapse.

The script imports the source-shaped finite model from Proof 266.  It checks
the complete three-branch factorization N_W=L_W^*K, replaces Gamma^(-1) by two
columns over powers of D=Delta^(1/2), and verifies the right-column isometry.

A direct-sum guard shows why an ordinary operator-norm observability estimate
cannot bound the trace.  The source theorem still needs compact-root control
of the complete left column before taking the trace.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_266() -> ModuleType:
    path = Path(__file__).with_name(
        "266_three_branch_causal_determinant_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_266_for_270", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_266 = load_proof_266()


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    hermitian = (matrix + matrix.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(hermitian)
    if float(eigenvalues.min()) < -1e-10:
        raise ValueError("matrix has a negative eigenvalue")
    return (
        eigenvectors
        @ np.diag(np.sqrt(np.maximum(eigenvalues, 0.0)))
        @ eigenvectors.conj().T
    )


def causal_inverse(multiplicity: int, diagonal: float) -> np.ndarray:
    off_diagonal = 0.25 * (1.0 - diagonal)
    jordan = np.array(
        [[diagonal, off_diagonal], [0.0, diagonal]],
        dtype=complex,
    )
    return np.kron(jordan, np.eye(multiplicity, dtype=complex))


def owner_data(
    model: dict[str, np.ndarray], inverse: np.ndarray | None = None
) -> dict[str, np.ndarray]:
    identity = model["identity"]
    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    band = model["B"]
    second_support = model["Q"]
    detector = model["W"]
    band_basis = model["b_basis"]
    causal = model["A"] if inverse is None else inverse

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
        causal @ sonin @ detector @ second_support @ band_basis
    )
    left = left_outer + left_second + left_prolate

    gamma = survivor.conj().T @ survivor
    identity_band = np.eye(band_basis.shape[1], dtype=complex)
    delta = identity_band - gamma
    defect = positive_square_root(delta)
    detector_band = band_basis.conj().T @ detector @ band_basis
    centered_numerator = (
        survivor.conj().T @ detector @ survivor
        - detector_band @ gamma
    )

    return {
        "K": survivor,
        "L_outer": left_outer,
        "L_second": left_second,
        "L_prolate": left_prolate,
        "L": left,
        "Gamma": gamma,
        "Delta": delta,
        "D": defect,
        "N": centered_numerator,
    }


def column_certificate(
    data: dict[str, np.ndarray], maximum_power: int, tail_tolerance: float
) -> tuple[dict[str, float], list[dict[str, float]]]:
    survivor = data["K"]
    left = data["L"]
    gamma = data["Gamma"]
    delta = data["Delta"]
    defect = data["D"]
    numerator = data["N"]
    identity = np.eye(gamma.shape[0], dtype=complex)

    complete_response = np.trace(numerator @ np.linalg.inv(gamma))
    right_gram = np.zeros_like(gamma)
    left_gram = np.zeros_like(gamma)
    pair_trace = 0.0j
    defect_power = identity.copy()
    selected_powers = {
        power
        for power in (0, 1, 2, 4, 8, 16, 32, 64, 128, maximum_power)
        if power <= maximum_power
    }
    rows: list[dict[str, float]] = []

    for exponent in range(maximum_power + 1):
        right_leg = survivor @ defect_power
        left_leg = left @ defect_power
        right_gram += right_leg.conj().T @ right_leg
        left_gram += left_leg.conj().T @ left_leg
        pair_trace += np.trace(left_leg.conj().T @ right_leg)
        if exponent in selected_powers:
            rows.append(
                {
                    "power": float(exponent),
                    "right_error": relative_error(right_gram, identity),
                    "pair_error": relative_error(
                        pair_trace, complete_response
                    ),
                    "left_norm": float(
                        np.linalg.norm(left_gram, ord=2)
                    ),
                    "left_trace": float(np.trace(left_gram).real),
                }
            )
        defect_power = defect_power @ defect
        if (
            exponent >= max(selected_powers)
            and float(np.linalg.norm(defect_power, ord=2))
            <= tail_tolerance
        ):
            break

    stein_residual = left_gram - left.conj().T @ left - (
        defect @ left_gram @ defect
    )
    gamma_eigenvalues, gamma_eigenvectors = np.linalg.eigh(
        (gamma + gamma.conj().T) / 2.0
    )
    gamma_inverse_square_root = (
        gamma_eigenvectors
        @ np.diag(gamma_eigenvalues**-0.5)
        @ gamma_eigenvectors.conj().T
    )
    one_step_domination = float(
        np.linalg.norm(
            gamma_inverse_square_root
            @ (left.conj().T @ left)
            @ gamma_inverse_square_root,
            ord=2,
        )
    )

    checks = {
        "three-branch left factor error": relative_error(
            left.conj().T @ survivor, numerator
        ),
        "defect square error": relative_error(
            defect @ defect, delta
        ),
        "right column isometry error": relative_error(
            right_gram, identity
        ),
        "column pairing trace error": relative_error(
            pair_trace, complete_response
        ),
        "Stein equation error": relative_error(
            stein_residual, np.zeros_like(stein_residual)
        ),
        "Gamma minimum eigenvalue": float(gamma_eigenvalues.min()),
        "Delta norm": float(np.linalg.norm(delta, ord=2)),
        "left observability norm": float(
            np.linalg.norm(left_gram, ord=2)
        ),
        "left observability trace": float(np.trace(left_gram).real),
        "one-step Gamma domination": one_step_domination,
        "complete response magnitude": float(abs(complete_response)),
        "outer left norm": float(np.linalg.norm(data["L_outer"], ord=2)),
        "second left norm": float(np.linalg.norm(data["L_second"], ord=2)),
        "prolate left norm": float(np.linalg.norm(data["L_prolate"], ord=2)),
        "complete left norm": float(np.linalg.norm(left, ord=2)),
    }
    return checks, rows


def conditioning_stress(
    multiplicity: int,
    seed: int,
    diagonals: tuple[float, ...],
    maximum_power: int,
    tail_tolerance: float,
) -> list[dict[str, float]]:
    model = PROOF_266.build_model(multiplicity, seed)
    rows: list[dict[str, float]] = []
    for diagonal in diagonals:
        inverse = causal_inverse(multiplicity, diagonal)
        data = owner_data(model, inverse)
        checks, _ = column_certificate(
            data, maximum_power, tail_tolerance
        )
        rows.append(
            {
                "diagonal": diagonal,
                "inverse_norm": float(np.linalg.norm(inverse, ord=2)),
                "gamma_minimum": checks["Gamma minimum eigenvalue"],
                "delta_norm": checks["Delta norm"],
                "observability_norm": checks[
                    "left observability norm"
                ],
                "domination": checks["one-step Gamma domination"],
            }
        )
    return rows


def direct_sum_guard(
    data: dict[str, np.ndarray], copies: tuple[int, ...]
) -> list[dict[str, float]]:
    survivor = data["K"]
    left = data["L"]
    gamma = data["Gamma"]
    defect = data["D"]
    numerator = data["N"]

    left_gram = np.zeros_like(gamma)
    power = np.eye(gamma.shape[0], dtype=complex)
    for _ in range(10_000):
        left_gram += power @ (left.conj().T @ left) @ power
        power = power @ defect
        if float(np.linalg.norm(power, ord=2)) < 1e-14:
            break
    response = np.trace(numerator @ np.linalg.inv(gamma))
    observability_norm = float(np.linalg.norm(left_gram, ord=2))
    observability_trace = float(np.trace(left_gram).real)
    rows: list[dict[str, float]] = []
    for count in copies:
        rows.append(
            {
                "copies": float(count),
                "response": count * float(abs(response)),
                "observability_norm": observability_norm,
                "observability_trace": count * observability_trace,
                "right_hs_norm": math.sqrt(count * gamma.shape[0]),
            }
        )
    return rows


def print_checks(checks: dict[str, float]) -> None:
    print("Renewal observability checks")
    print("+--------------------------------------------+---------------+")
    print("| check                                      | value         |")
    print("+--------------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>13.6e} |")
    print("+--------------------------------------------+---------------+")


def print_convergence(rows: list[dict[str, float]]) -> None:
    print("Column convergence")
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )
    print(
        "| power  | right error   | pair error    | left norm     | left trace    |"
    )
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['power']):>6d} |"
            f" {row['right_error']:>13.6e} |"
            f" {row['pair_error']:>13.6e} |"
            f" {row['left_norm']:>13.6e} |"
            f" {row['left_trace']:>13.6e} |"
        )
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )


def print_stress(rows: list[dict[str, float]]) -> None:
    print("Causal conditioning stress")
    print(
        "+----------+----------+-------------+-------------+-------------+-------------+"
    )
    print(
        "| diagonal | norm A   | min Gamma   | norm Delta  | obs norm    | domination  |"
    )
    print(
        "+----------+----------+-------------+-------------+-------------+-------------+"
    )
    for row in rows:
        print(
            f"| {row['diagonal']:>8.2f} |"
            f" {row['inverse_norm']:>8.5f} |"
            f" {row['gamma_minimum']:>11.4e} |"
            f" {row['delta_norm']:>11.4e} |"
            f" {row['observability_norm']:>11.4e} |"
            f" {row['domination']:>11.4e} |"
        )
    print(
        "+----------+----------+-------------+-------------+-------------+-------------+"
    )


def print_guard(rows: list[dict[str, float]]) -> None:
    print("Direct-sum trace guard")
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )
    print(
        "| copies | response      | obs op norm   | obs trace     | right HS norm |"
    )
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['copies']):>6d} |"
            f" {row['response']:>13.6e} |"
            f" {row['observability_norm']:>13.6e} |"
            f" {row['observability_trace']:>13.6e} |"
            f" {row['right_hs_norm']:>13.6e} |"
        )
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=8)
    parser.add_argument("--seed", type=int, default=270)
    parser.add_argument("--maximum-power", type=int, default=10_000)
    parser.add_argument("--tail-tolerance", type=float, default=1e-14)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    model = PROOF_266.build_model(args.multiplicity, args.seed)
    data = owner_data(model)
    checks, convergence = column_certificate(
        data, args.maximum_power, args.tail_tolerance
    )
    stress = conditioning_stress(
        args.multiplicity,
        args.seed + 1,
        (0.10, 0.25, 0.50, 0.75, 0.90, 0.97),
        args.maximum_power,
        args.tail_tolerance,
    )
    guard = direct_sum_guard(data, (1, 2, 4, 8, 16))

    print("identity=renewal inverse as an observability column")
    print("status=exact fixed-S algebra; source column estimate open")
    print_checks(checks)
    print()
    print_convergence(convergence)
    print()
    print_stress(stress)
    print()
    print_guard(guard)

    exact_errors = [
        checks["three-branch left factor error"],
        checks["defect square error"],
        checks["right column isometry error"],
        checks["column pairing trace error"],
        checks["Stein equation error"],
    ]
    maximum_error = max(exact_errors)
    print(f"maximum exact error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"observability certificate failed: {maximum_error:.6e}"
        )
    if guard[-1]["response"] <= 8.0 * guard[0]["response"]:
        raise SystemExit("direct-sum trace guard stopped growing")
    if abs(
        guard[-1]["observability_norm"]
        - guard[0]["observability_norm"]
    ) > args.tolerance:
        raise SystemExit("direct-sum observability norm changed")

    print("three_branch_left_factor_verdict=EXACT")
    print("right_survivor_column_verdict=ISOMETRY")
    print("ordinary_observability_operator_norm_verdict=INSUFFICIENT")
    print("positive_h1_column_estimate=REJECTED_BY_PROOF_273")
    print("signed_scalar_local_coefficient=p^(-m/2)")
    print("complete_signed_extra_half_power=OPEN")
    print("signed_paired_source_disintegration=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
