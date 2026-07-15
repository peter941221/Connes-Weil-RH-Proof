#!/usr/bin/env python3
"""Certificate for the causal boundary numerator and renewal response.

For K = E A B and Gamma = K* K, Proof 264 gives the ordered Gram response

    Tr_B(K* W K Gamma^-1 - B W B).

This certificate verifies that its centered numerator is exactly one outer
detector crossing minus one Sonin detector crossing.  After normalizing the
causal inverse A to a contraction, Gamma is positive and its inverse
has a fixed-S renewal expansion.  The expansion is an algebraic certificate,
not a uniform estimate: taking absolute values term by term recovers the
forbidden inverse lower bound.
"""

from __future__ import annotations

import argparse

import numpy as np


def basis_block(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def metric_projection(
    source: np.ndarray, transport: np.ndarray, metric: np.ndarray
) -> np.ndarray:
    identity = np.eye(source.shape[0], dtype=complex)
    inverse = np.linalg.inv(source @ metric @ source + identity - source)
    return transport @ source @ inverse @ source @ transport.conj().T


def renewal_certificate(
    size: int, seed: int, maximum_power: int
) -> tuple[dict[str, float], list[dict[str, float]]]:
    if size < 12:
        raise ValueError("renewal certificate size must be at least 12")
    if maximum_power < 8:
        raise ValueError("maximum renewal power must be at least eight")

    rng = np.random.default_rng(seed)
    c_rank = size // 4
    e_rank = size - c_rank
    r_rank = e_rank // 3
    c_basis = basis_block(size, 0, c_rank)
    e_basis = basis_block(size, c_rank, size)
    c_projection = projection(c_basis)
    e_projection = projection(e_basis)

    random_e = rng.normal(size=(e_rank, e_rank)) + 1j * rng.normal(
        size=(e_rank, e_rank)
    )
    e_unitary, _ = np.linalg.qr(random_e)
    r_basis = e_basis @ e_unitary[:, :r_rank]
    b_basis = e_basis @ e_unitary[:, r_rank:]
    r_projection = projection(r_basis)
    b_projection = projection(b_basis)

    amplitudes = np.linspace(0.72, 0.96, size)
    phases = np.linspace(-0.8, 0.6, size)
    inverse_values = amplitudes * np.exp(1j * phases)
    causal_inverse = np.diag(inverse_values)
    transport = np.diag(1.0 / inverse_values)
    metric = transport.conj().T @ transport

    detector_values = 0.4 + np.linspace(-0.7, 1.0, size) ** 2
    detector = np.diag(detector_values)
    detector_b = b_basis.conj().T @ detector @ b_basis

    killed_band = e_projection @ causal_inverse @ b_basis
    covariance = killed_band.conj().T @ killed_band
    inverse_covariance = np.linalg.inv(covariance)
    weighted_covariance = (
        killed_band.conj().T @ detector @ killed_band
    )
    centered_numerator = weighted_covariance - detector_b @ covariance
    gram_operator = (
        weighted_covariance @ inverse_covariance - detector_b
    )
    gram_response = np.trace(gram_operator)

    outer_numerator = (
        -b_basis.conj().T
        @ causal_inverse.conj().T
        @ c_projection
        @ detector
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    sonin_numerator = (
        b_basis.conj().T
        @ detector
        @ r_projection
        @ causal_inverse.conj().T
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    boundary_numerator = outer_numerator + sonin_numerator

    outer_commutator = (
        -b_basis.conj().T
        @ causal_inverse.conj().T
        @ c_projection
        @ commutator(detector, e_projection)
        @ e_projection
        @ causal_inverse
        @ b_basis
    )
    sonin_commutator = (
        b_basis.conj().T
        @ commutator(detector, r_projection)
        @ r_projection
        @ causal_inverse.conj().T
        @ e_projection
        @ causal_inverse
        @ b_basis
    )

    transported_outer = metric_projection(
        e_projection, transport, metric
    )
    transported_inner = metric_projection(
        r_projection, transport, metric
    )
    direct_response = np.trace(
        detector
        @ (transported_outer - transported_inner - b_projection)
    )

    identity_b = np.eye(b_basis.shape[1], dtype=complex)
    defect = identity_b - covariance
    defect_norm = float(np.linalg.norm(defect, ord=2))
    covariance_eigenvalues = np.linalg.eigvalsh(
        (covariance + covariance.conj().T) / 2.0
    )

    selected_powers = sorted(
        {0, 1, 2, 4, 8, 16, 32, maximum_power}
    )
    selected_powers = [
        power for power in selected_powers if power <= maximum_power
    ]
    renewal_rows: list[dict[str, float]] = []
    power = identity_b.copy()
    partial_operator = np.zeros_like(covariance)
    selected = set(selected_powers)
    for exponent in range(maximum_power + 1):
        partial_operator += centered_numerator @ power
        if exponent in selected:
            partial_response = np.trace(partial_operator)
            renewal_rows.append(
                {
                    "power": float(exponent),
                    "response_real": float(partial_response.real),
                    "response_imag": float(partial_response.imag),
                    "operator_error": relative_error(
                        partial_operator, gram_operator
                    ),
                    "response_error": relative_error(
                        partial_response, gram_response
                    ),
                }
            )
        power = power @ defect

    final_operator_error = renewal_rows[-1]["operator_error"]
    return (
        {
            "normality_error": float(
                np.linalg.norm(
                    causal_inverse.conj().T @ causal_inverse
                    - causal_inverse @ causal_inverse.conj().T
                )
            ),
            "detector_transport_commutator": float(
                np.linalg.norm(detector @ transport - transport @ detector)
            ),
            "preserved_complement_error": float(
                np.linalg.norm(
                    e_projection @ causal_inverse @ c_projection
                )
            ),
            "covariance_upper_violation": max(
                0.0, float(covariance_eigenvalues.max() - 1.0)
            ),
            "covariance_lower_bound": float(
                covariance_eigenvalues.min()
            ),
            "defect_norm": defect_norm,
            "boundary_numerator_error": relative_error(
                boundary_numerator, centered_numerator
            ),
            "commutator_numerator_error": relative_error(
                outer_commutator + sonin_commutator,
                centered_numerator,
            ),
            "gram_operator_error": relative_error(
                centered_numerator @ inverse_covariance,
                gram_operator,
            ),
            "direct_response_error": relative_error(
                gram_response, direct_response
            ),
            "renewal_final_operator_error": final_operator_error,
        },
        renewal_rows,
    )


def print_report(
    checks: dict[str, float], rows: list[dict[str, float]]
) -> None:
    print("causal boundary numerator")
    print("+--------------------------------------+---------------+")
    print("| check                                | value         |")
    print("+--------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<36} | {value:>13.6e} |")
    print("+--------------------------------------+---------------+")

    print()
    print("fixed-S signed renewal partial sums")
    print("+-------+-------------+-------------+-------------+-------------+")
    print("| power | response Re | response Im | operator err| response err|")
    print("+-------+-------------+-------------+-------------+-------------+")
    for row in rows:
        print(
            f"| {int(row['power']):>5} "
            f"| {row['response_real']:>11.5e} "
            f"| {row['response_imag']:>11.5e} "
            f"| {row['operator_error']:>11.5e} "
            f"| {row['response_error']:>11.5e} |"
        )
    print("+-------+-------------+-------------+-------------+-------------+")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--seed", type=int, default=265)
    parser.add_argument("--maximum-power", type=int, default=48)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    checks, rows = renewal_certificate(
        args.size, args.seed, args.maximum_power
    )
    print_report(checks, rows)

    algebra_keys = (
        "normality_error",
        "detector_transport_commutator",
        "preserved_complement_error",
        "covariance_upper_violation",
        "boundary_numerator_error",
        "commutator_numerator_error",
        "gram_operator_error",
        "direct_response_error",
        "renewal_final_operator_error",
    )
    maximum_error = max(checks[key] for key in algebra_keys)
    print(f"maximum checked error: {maximum_error:.6e}")
    if checks["defect_norm"] >= 1.0:
        raise SystemExit("certificate failed: renewal defect is not contractive")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
