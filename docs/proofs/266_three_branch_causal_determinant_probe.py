#!/usr/bin/env python3
"""Algebra certificate for the three-branch causal determinant owner.

The model enforces the identities used by Proof 266:

    R <= E, R <= Q,
    E Q E = R + K_prol,
    (B Q)(B Q)* = K_prol on B,
    C A* E = 0,
    [A, W] = [A*, W] = 0.

It verifies that Proof 265's centered Gram numerator is the sum of the
outer-boundary, second-support, and prolate branches before every common
renewal power.  It also checks the derivative of the finite-dimensional
relative Gram determinant.  This is an algebra certificate only; finite
matrices do not prove the source uniform estimate.
"""

from __future__ import annotations

import argparse

import numpy as np


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def hermitian_exponential(matrix: np.ndarray, parameter: float) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    return (
        eigenvectors
        @ np.diag(np.exp(parameter * eigenvalues))
        @ eigenvectors.conj().T
    )


def build_model(
    multiplicity: int, seed: int
) -> dict[str, np.ndarray]:
    if multiplicity < 6 or multiplicity % 2 != 0:
        raise ValueError("multiplicity must be even and at least six")

    rng = np.random.default_rng(seed)
    size = 2 * multiplicity
    c_rank = multiplicity // 2
    b_rank = c_rank
    r_rank = size - c_rank - b_rank

    identity = np.eye(size, dtype=complex)
    c_basis = identity[:, :c_rank]
    e_basis = identity[:, c_rank:]
    c_projection = projection(c_basis)
    e_projection = projection(e_basis)

    random_e = rng.normal(size=(e_basis.shape[1], e_basis.shape[1]))
    random_e = random_e + 1j * rng.normal(size=random_e.shape)
    e_unitary, _ = np.linalg.qr(random_e)
    r_basis = e_basis @ e_unitary[:, :r_rank]
    b_basis = e_basis @ e_unitary[:, r_rank:]
    r_projection = projection(r_basis)
    b_projection = projection(b_basis)

    # A repeated Jordan block gives a finite causal algebra model.  W acts on
    # the multiplicity factor, so it commutes with both A and A* while still
    # crossing the chosen C/E boundary.
    jordan = np.array([[0.78, 0.08], [0.0, 0.78]], dtype=complex)
    causal_inverse = np.kron(jordan, np.eye(multiplicity, dtype=complex))

    random_w = rng.normal(size=(multiplicity, multiplicity))
    random_w = random_w + 1j * rng.normal(size=random_w.shape)
    random_w = (random_w + random_w.conj().T) / 2.0
    random_w /= max(float(np.linalg.norm(random_w, ord=2)), 1.0)
    detector_factor = 1.4 * np.eye(multiplicity) + 0.25 * random_w
    detector = np.kron(np.eye(2, dtype=complex), detector_factor)

    prolate_singular_values = np.exp(
        -0.45 * np.arange(1, b_rank + 1, dtype=float) ** 1.35
    )
    q_graph = (
        b_basis @ np.diag(prolate_singular_values)
        + c_basis
        @ np.diag(np.sqrt(1.0 - prolate_singular_values**2))
    )
    q_basis = np.column_stack((r_basis, q_graph))
    q_projection = projection(q_basis)
    prolate = b_projection @ q_projection @ b_projection

    return {
        "identity": identity,
        "C": c_projection,
        "E": e_projection,
        "R": r_projection,
        "B": b_projection,
        "Q": q_projection,
        "K_prol": prolate,
        "A": causal_inverse,
        "W": detector,
        "b_basis": b_basis,
    }


def certificate(
    multiplicity: int, seed: int, maximum_power: int, step: float
) -> tuple[dict[str, float], list[dict[str, float]]]:
    model = build_model(multiplicity, seed)
    c_projection = model["C"]
    e_projection = model["E"]
    r_projection = model["R"]
    b_projection = model["B"]
    q_projection = model["Q"]
    prolate = model["K_prol"]
    causal_inverse = model["A"]
    detector = model["W"]
    b_basis = model["b_basis"]

    killed_band = e_projection @ causal_inverse @ b_basis
    gamma = killed_band.conj().T @ killed_band
    inverse_gamma = np.linalg.inv(gamma)
    detector_b = b_basis.conj().T @ detector @ b_basis
    weighted_gamma = killed_band.conj().T @ detector @ killed_band
    centered_numerator = weighted_gamma - detector_b @ gamma

    outer = (
        -b_basis.conj().T
        @ causal_inverse.conj().T
        @ c_projection
        @ commutator(detector, e_projection)
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    sonin = (
        b_basis.conj().T
        @ commutator(detector, r_projection)
        @ r_projection
        @ causal_inverse.conj().T
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    prolate_branch = (
        b_basis.conj().T
        @ q_projection
        @ detector
        @ r_projection
        @ causal_inverse.conj().T
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    second_support_branch = (
        b_basis.conj().T
        @ (model["identity"] - q_projection)
        @ commutator(detector, q_projection)
        @ r_projection
        @ causal_inverse.conj().T
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    three_branch_numerator = outer + prolate_branch + second_support_branch

    identity_b = np.eye(b_basis.shape[1], dtype=complex)
    delta = identity_b - gamma
    delta_norm = float(np.linalg.norm(delta, ord=2))
    gamma_eigenvalues = np.linalg.eigvalsh((gamma + gamma.conj().T) / 2.0)

    selected_powers = sorted(
        power
        for power in {0, 1, 2, 4, 8, 16, 32, 64, maximum_power}
        if power <= maximum_power
    )
    rows: list[dict[str, float]] = []
    power = identity_b.copy()
    partial_three_branch = np.zeros_like(gamma)
    complete_operator = centered_numerator @ inverse_gamma
    for exponent in range(maximum_power + 1):
        partial_three_branch += three_branch_numerator @ power
        if exponent in selected_powers:
            rows.append(
                {
                    "power": float(exponent),
                    "response_real": float(
                        np.trace(partial_three_branch).real
                    ),
                    "response_imag": float(
                        np.trace(partial_three_branch).imag
                    ),
                    "operator_error": relative_error(
                        partial_three_branch, complete_operator
                    ),
                    "common_branch_error": relative_error(
                        (outer + sonin) @ power,
                        three_branch_numerator @ power,
                    ),
                }
            )
        power = power @ delta

    def relative_log_determinant(parameter: float) -> complex:
        exponential = hermitian_exponential(detector, parameter)
        gamma_s = killed_band.conj().T @ exponential @ killed_band
        b_s = b_basis.conj().T @ exponential @ b_basis
        relative = gamma_s @ inverse_gamma @ np.linalg.inv(b_s)
        return np.log(np.linalg.det(relative))

    determinant_derivative = (
        relative_log_determinant(step)
        - relative_log_determinant(-step)
    ) / (2.0 * step)
    response = np.trace(complete_operator)

    checks = {
        "A_contraction_violation": max(
            0.0, float(np.linalg.norm(causal_inverse, ord=2) - 1.0)
        ),
        "detector_A_commutator": float(
            np.linalg.norm(commutator(detector, causal_inverse))
        ),
        "detector_Astar_commutator": float(
            np.linalg.norm(commutator(detector, causal_inverse.conj().T))
        ),
        "causal_orientation_error": float(
            np.linalg.norm(
                c_projection @ causal_inverse.conj().T @ e_projection
            )
        ),
        "QR_error": relative_error(q_projection @ r_projection, r_projection),
        "EQE_error": relative_error(
            e_projection @ q_projection @ e_projection,
            r_projection + prolate,
        ),
        "prolate_square_error": relative_error(
            (b_projection @ q_projection)
            @ (b_projection @ q_projection).conj().T,
            prolate,
        ),
        "centered_numerator_error": relative_error(
            outer + sonin, centered_numerator
        ),
        "sonin_split_error": relative_error(
            prolate_branch + second_support_branch, sonin
        ),
        "three_branch_numerator_error": relative_error(
            three_branch_numerator, centered_numerator
        ),
        "relative_determinant_derivative_error": relative_error(
            determinant_derivative, response
        ),
        "renewal_final_operator_error": rows[-1]["operator_error"],
        "gamma_lower_bound": float(gamma_eigenvalues.min()),
        "delta_norm": delta_norm,
        "outer_branch_norm": float(np.linalg.norm(outer, ord="nuc")),
        "second_support_branch_norm": float(
            np.linalg.norm(second_support_branch, ord="nuc")
        ),
        "prolate_branch_norm": float(
            np.linalg.norm(prolate_branch, ord="nuc")
        ),
        "complete_numerator_norm": float(
            np.linalg.norm(three_branch_numerator, ord="nuc")
        ),
    }
    return checks, rows


def print_report(
    checks: dict[str, float], rows: list[dict[str, float]]
) -> None:
    print("three-branch causal determinant checks")
    print("+-----------------------------------------+---------------+")
    print("| check                                   | value         |")
    print("+-----------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<39} | {value:>13.6e} |")
    print("+-----------------------------------------+---------------+")

    print()
    print("common three-branch renewal")
    print("+-------+-------------+-------------+-------------+-------------+")
    print("| power | response Re | response Im | operator err| branch err  |")
    print("+-------+-------------+-------------+-------------+-------------+")
    for row in rows:
        print(
            f"| {int(row['power']):>5} "
            f"| {row['response_real']:>11.5e} "
            f"| {row['response_imag']:>11.5e} "
            f"| {row['operator_error']:>11.5e} "
            f"| {row['common_branch_error']:>11.5e} |"
        )
    print("+-------+-------------+-------------+-------------+-------------+")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=8)
    parser.add_argument("--seed", type=int, default=266)
    parser.add_argument("--maximum-power", type=int, default=96)
    parser.add_argument("--step", type=float, default=1e-6)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    args = parser.parse_args()

    checks, rows = certificate(
        args.multiplicity, args.seed, args.maximum_power, args.step
    )
    print_report(checks, rows)

    algebra_keys = (
        "A_contraction_violation",
        "detector_A_commutator",
        "detector_Astar_commutator",
        "causal_orientation_error",
        "QR_error",
        "EQE_error",
        "prolate_square_error",
        "centered_numerator_error",
        "sonin_split_error",
        "three_branch_numerator_error",
        "relative_determinant_derivative_error",
        "renewal_final_operator_error",
    )
    maximum_error = max(checks[key] for key in algebra_keys)
    print(f"maximum checked error: {maximum_error:.6e}")
    if checks["gamma_lower_bound"] <= 0.0:
        raise SystemExit("certificate failed: Gamma is not positive definite")
    if checks["delta_norm"] >= 1.0:
        raise SystemExit("certificate failed: renewal defect is not contractive")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
