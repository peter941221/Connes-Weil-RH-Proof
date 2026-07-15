#!/usr/bin/env python3
"""Non-periodic response probe for the Gate 3U endpoint owner.

The first layer verifies Proof 262's endpoint two-commutator identity on a
Hermite spectral model of the real line.  Translations are represented by
their exact Fourier multipliers exp(-i b xi); prime logarithms are never
rounded to grid cells and there is no periodic wraparound.

The second layer keeps the complete finite Euler product whole.  Each local
factor is applied to the transported outer and Sonin bases before a QR step,
which preserves the exact finite-dimensional range without accumulating the
Euler condition number.  It then samples the regularized translation response

    kappa_(N,S)(z) = Tr(U_z (B_(N,S) - B_(N,0)))

on one compact displacement interval.  This finite-dimensional kappa is only
a diagnostic regularization of the response distribution; the corresponding
raw infinite-dimensional trace need not exist.

The final layer gives an explicit negative 2 by 2 minor for the p=2,3
two-sided geometric kernel ordered by n log(2) + m log(3).  It permanently
guards against replacing the required causal half-line argument by an
incorrect total-positivity assertion on the full prime-log group.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_251() -> ModuleType:
    path = Path(__file__).with_name(
        "251_mixed_prime_projection_curvature_probe.py"
    )
    spec = importlib.util.spec_from_file_location("proof_251", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_251 = load_proof_251()


def parse_positive_integers(raw: str) -> list[int]:
    values = [int(item) for item in raw.split(",") if item.strip()]
    if not values or any(value <= 0 for value in values):
        raise ValueError("expected a nonempty list of positive integers")
    return values


def primes_up_to(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        is_prime = True
        for prime in primes:
            if prime * prime > candidate:
                break
            if candidate % prime == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(candidate)
    return primes


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1e-15)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


@dataclass(frozen=True)
class HermiteSourceModel:
    coordinates: np.ndarray
    fourier: np.ndarray
    scattering: np.ndarray
    outer_columns: np.ndarray
    sonin_columns: np.ndarray
    band_columns: np.ndarray
    outer: np.ndarray
    sonin: np.ndarray
    second_support: np.ndarray
    band: np.ndarray
    fourier_unitarity_error: float
    scattering_unitarity_error: float
    nesting_error: float
    factor_invariance_residual: float


def hermite_source_model(
    size: int, intersection_tolerance: float
) -> HermiteSourceModel:
    if size < 16 or size % 2:
        raise ValueError("Hermite size must be even and at least 16")

    coordinates, weights = np.polynomial.hermite.hermgauss(size)
    polynomials = np.empty((size, size), dtype=float)
    polynomials[:, 0] = math.pi ** (-0.25)
    polynomials[:, 1] = math.sqrt(2.0) * coordinates * polynomials[:, 0]
    for degree in range(1, size - 1):
        polynomials[:, degree + 1] = (
            math.sqrt(2.0 / (degree + 1.0))
            * coordinates
            * polynomials[:, degree]
            - math.sqrt(degree / (degree + 1.0))
            * polynomials[:, degree - 1]
        )

    evaluation = np.sqrt(weights)[:, None] * polynomials
    fourier_eigenvalues = (-1j) ** np.arange(size)
    fourier = (
        evaluation
        @ np.diag(fourier_eigenvalues)
        @ evaluation.conj().T
    )
    identity = np.eye(size, dtype=complex)
    fourier_unitarity_error = float(
        np.linalg.norm(fourier.conj().T @ fourier - identity, ord="fro")
    )

    scattering_multiplier = PROOF_251.archimedean_scattering(coordinates)
    scattering = (
        fourier.conj().T
        @ np.diag(scattering_multiplier)
        @ fourier
    )
    scattering_unitarity_error = float(
        np.linalg.norm(
            scattering.conj().T @ scattering - identity, ord="fro"
        )
    )

    positive_indices = np.flatnonzero(coordinates >= 0.0)
    outer_columns = identity[:, positive_indices]
    outer = orthogonal_projection(outer_columns)
    second_support = scattering.conj().T @ outer @ scattering

    angle = outer_columns.conj().T @ second_support @ outer_columns
    angle = (angle + angle.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(angle)
    selected = eigenvalues > 1.0 - intersection_tolerance
    sonin_columns = outer_columns @ eigenvectors[:, selected]
    band_columns = outer_columns @ eigenvectors[:, ~selected]
    sonin = orthogonal_projection(sonin_columns)
    band = orthogonal_projection(band_columns)
    nesting_error = float(
        np.linalg.norm(outer @ sonin - sonin, ord="fro")
    )

    first_prime = 2
    translation = spectral_translation(
        coordinates, fourier, math.log(first_prime)
    )
    first_factor = identity - first_prime ** (-0.5) * translation
    factor_invariance_residual = float(
        np.linalg.norm(
            (identity - second_support)
            @ first_factor
            @ second_support,
            ord=2,
        )
    )

    return HermiteSourceModel(
        coordinates=coordinates,
        fourier=fourier,
        scattering=scattering,
        outer_columns=outer_columns,
        sonin_columns=sonin_columns,
        band_columns=band_columns,
        outer=outer,
        sonin=sonin,
        second_support=second_support,
        band=band,
        fourier_unitarity_error=fourier_unitarity_error,
        scattering_unitarity_error=scattering_unitarity_error,
        nesting_error=nesting_error,
        factor_invariance_residual=factor_invariance_residual,
    )


def spectral_translation(
    coordinates: np.ndarray, fourier: np.ndarray, displacement: float
) -> np.ndarray:
    multiplier = np.exp(-1j * displacement * coordinates)
    return fourier.conj().T @ np.diag(multiplier) @ fourier


def apply_spectral_translation(
    model: HermiteSourceModel,
    displacement: float,
    columns: np.ndarray,
) -> np.ndarray:
    multiplier = np.exp(-1j * displacement * model.coordinates)
    return model.fourier.conj().T @ (
        multiplier[:, None] * (model.fourier @ columns)
    )


def transport_columns_by_prime(
    model: HermiteSourceModel, columns: np.ndarray, prime: int
) -> np.ndarray:
    transported = columns - prime ** (-0.5) * apply_spectral_translation(
        model, math.log(prime), columns
    )
    orthonormal, _ = np.linalg.qr(transported, mode="reduced")
    return orthonormal


def response_samples(
    model: HermiteSourceModel,
    transported_outer: np.ndarray,
    transported_sonin: np.ndarray,
    response_radius: float,
    response_points: int,
) -> dict[str, float]:
    transported_band = (
        orthogonal_projection(transported_outer)
        - orthogonal_projection(transported_sonin)
    )
    difference = transported_band - model.band
    difference = (difference + difference.conj().T) / 2.0

    frequency_difference = (
        model.fourier @ difference @ model.fourier.conj().T
    )
    coefficients = np.diag(frequency_difference)
    displacements = np.linspace(
        -response_radius, response_radius, response_points
    )
    response = (
        np.exp(-1j * np.outer(displacements, model.coordinates))
        @ coefficients
    )
    reverse_response = response[::-1]
    hermitian_error = relative_error(reverse_response, np.conj(response))
    zero_index = int(np.argmin(np.abs(displacements)))
    local_l2 = float(
        np.trapz(np.abs(response) ** 2, displacements) ** 0.5
    )

    return {
        "response_max": float(np.max(np.abs(response))),
        "response_l2": local_l2,
        "response_at_zero": float(abs(response[zero_index])),
        "response_hermitian_error": hermitian_error,
        "rank_trace_error": float(abs(np.trace(difference))),
        "difference_operator_norm": float(np.linalg.norm(difference, ord=2)),
        "difference_frobenius_norm": float(
            np.linalg.norm(difference, ord="fro")
        ),
    }


def response_cohorts(
    model: HermiteSourceModel,
    prime_limits: list[int],
    response_radius: float,
    response_points: int,
) -> list[dict[str, float]]:
    primes = primes_up_to(max(prime_limits))
    final_prime_by_limit = {
        limit: max(prime for prime in primes if prime <= limit)
        for limit in prime_limits
    }
    limits_by_final_prime: dict[int, list[int]] = {}
    for limit, final_prime in final_prime_by_limit.items():
        limits_by_final_prime.setdefault(final_prime, []).append(limit)

    transported_outer = model.outer_columns.copy()
    transported_sonin = model.sonin_columns.copy()
    rows: list[dict[str, float]] = []
    prime_count = 0

    for prime in primes:
        transported_outer = transport_columns_by_prime(
            model, transported_outer, prime
        )
        transported_sonin = transport_columns_by_prime(
            model, transported_sonin, prime
        )
        prime_count += 1
        for limit in limits_by_final_prime.get(prime, []):
            statistics = response_samples(
                model,
                transported_outer,
                transported_sonin,
                response_radius,
                response_points,
            )
            rows.append(
                {
                    "prime_limit": float(limit),
                    "prime_count": float(prime_count),
                    **statistics,
                }
            )

    return sorted(rows, key=lambda row: row["prime_limit"])


def direct_transport(
    model: HermiteSourceModel, prime_limit: int
) -> np.ndarray:
    multiplier = np.ones(len(model.coordinates), dtype=complex)
    for prime in primes_up_to(prime_limit):
        multiplier *= 1.0 - prime ** (-0.5) * np.exp(
            -1j * math.log(prime) * model.coordinates
        )
    return (
        model.fourier.conj().T
        @ np.diag(multiplier)
        @ model.fourier
    )


def endpoint_two_commutator_certificate(
    model: HermiteSourceModel,
    prime_limit: int,
    displacements: tuple[float, ...],
) -> dict[str, float]:
    identity = np.eye(len(model.coordinates), dtype=complex)
    complement = identity - model.outer
    transport = direct_transport(model, prime_limit)
    metric = transport.conj().T @ transport

    transported_outer_columns, _ = np.linalg.qr(
        transport @ model.outer_columns, mode="reduced"
    )
    transported_sonin_columns, _ = np.linalg.qr(
        transport @ model.sonin_columns, mode="reduced"
    )
    transported_band = (
        orthogonal_projection(transported_outer_columns)
        - orthogonal_projection(transported_sonin_columns)
    )

    inner_metric = (
        model.sonin_columns.conj().T
        @ metric
        @ model.sonin_columns
    )
    graph_coefficients = np.linalg.solve(
        inner_metric,
        model.sonin_columns.conj().T
        @ metric
        @ model.band_columns,
    )
    graph = (
        model.sonin_columns
        @ graph_coefficients
        @ model.band_columns.conj().T
    )
    source_frame_columns = (
        model.band_columns
        - model.sonin_columns @ graph_coefficients
    )
    schur = (
        source_frame_columns.conj().T
        @ metric
        @ source_frame_columns
    )
    coframe = (
        metric
        @ source_frame_columns
        @ np.linalg.inv(schur)
        @ model.band_columns.conj().T
    )

    maximum_response_error = 0.0
    maximum_commutation_error = 0.0
    for displacement in displacements:
        detector = spectral_translation(
            model.coordinates, model.fourier, displacement
        )
        direct_response = np.trace(
            detector @ (transported_band - model.band)
        )
        bracket = (
            complement
            @ commutator(detector, model.outer)
            @ model.band
            - commutator(detector, model.sonin)
            @ model.sonin
            @ graph
        )
        formula_response = np.trace(coframe.conj().T @ bracket)
        maximum_response_error = max(
            maximum_response_error,
            relative_error(formula_response, direct_response),
        )
        maximum_commutation_error = max(
            maximum_commutation_error,
            float(
                np.linalg.norm(
                    commutator(detector, transport), ord="fro"
                )
            ),
        )

    return {
        "two_commutator_response_error": maximum_response_error,
        "detector_transport_commutator": maximum_commutation_error,
        "coframe_sonin_orthogonality": float(
            np.linalg.norm(
                coframe.conj().T @ model.sonin, ord="fro"
            )
        ),
        "coframe_band_pairing_error": relative_error(
            coframe.conj().T @ model.band, model.band
        ),
        "inner_metric_condition": float(np.linalg.cond(inner_metric)),
        "schur_condition": float(np.linalg.cond(schur)),
    }


def prime_log_total_positivity_guard() -> dict[str, float]:
    first_x = (3, -4)
    second_x = (-4, 1)
    first_y = (-4, 1)
    second_y = (4, -4)

    def position(point: tuple[int, int]) -> float:
        return point[0] * math.log(2.0) + point[1] * math.log(3.0)

    def kernel(
        left: tuple[int, int], right: tuple[int, int]
    ) -> float:
        return (
            2.0 ** (-0.5 * abs(left[0] - right[0]))
            * 3.0 ** (-0.5 * abs(left[1] - right[1]))
        )

    determinant = (
        kernel(first_x, first_y) * kernel(second_x, second_y)
        - kernel(first_x, second_y) * kernel(second_x, first_y)
    )
    return {
        "x_order_margin": position(second_x) - position(first_x),
        "y_order_margin": position(second_y) - position(first_y),
        "ordered_minor": determinant,
    }


def print_report(
    models: list[tuple[HermiteSourceModel, list[dict[str, float]]]],
    certificate: dict[str, float],
    total_positivity: dict[str, float],
) -> None:
    print("Hermite whole-line endpoint response")
    print("+------+-------+-------+--------+--------+-------------+-------------+")
    print("| size | band  | p<=   | primes | max|k| | local L2    | |k(0)|      |")
    print("+------+-------+-------+--------+--------+-------------+-------------+")
    for model, rows in models:
        for row in rows:
            print(
                f"| {len(model.coordinates):>4} "
                f"| {model.band_columns.shape[1]:>5} "
                f"| {int(row['prime_limit']):>5} "
                f"| {int(row['prime_count']):>6} "
                f"| {row['response_max']:>6.3f} "
                f"| {row['response_l2']:>11.4e} "
                f"| {row['response_at_zero']:>11.4e} |"
            )
    print("+------+-------+-------+--------+--------+-------------+-------------+")

    print()
    print("finite-section source guards")
    print("+------+-------------+-------------+-------------+-------------+")
    print("| size | Fourier err | scatter err | nesting err | Q leak      |")
    print("+------+-------------+-------------+-------------+-------------+")
    for model, _rows in models:
        print(
            f"| {len(model.coordinates):>4} "
            f"| {model.fourier_unitarity_error:>11.4e} "
            f"| {model.scattering_unitarity_error:>11.4e} "
            f"| {model.nesting_error:>11.4e} "
            f"| {model.factor_invariance_residual:>11.4e} |"
        )
    print("+------+-------------+-------------+-------------+-------------+")

    print()
    print("endpoint two-commutator algebra")
    for key, value in certificate.items():
        print(f"{key}={value:.12e}")

    print()
    print("prime-log total-positivity guard")
    for key, value in total_positivity.items():
        print(f"{key}={value:.12e}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="64,96,128,160")
    parser.add_argument("--prime-limits", default="11,97,997,10000")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--response-radius", type=float, default=4.0)
    parser.add_argument("--response-points", type=int, default=1601)
    parser.add_argument("--certificate-prime-limit", type=int, default=11)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    args = parser.parse_args()

    sizes = parse_positive_integers(args.sizes)
    prime_limits = parse_positive_integers(args.prime_limits)
    if args.response_points < 3 or args.response_points % 2 == 0:
        raise ValueError("response-points must be odd and at least three")
    if args.response_radius <= 0.0:
        raise ValueError("response-radius must be positive")

    model_rows: list[tuple[HermiteSourceModel, list[dict[str, float]]]] = []
    for size in sizes:
        model = hermite_source_model(size, args.intersection_tolerance)
        rows = response_cohorts(
            model,
            prime_limits,
            args.response_radius,
            args.response_points,
        )
        model_rows.append((model, rows))

    certificate_model = model_rows[0][0]
    certificate = endpoint_two_commutator_certificate(
        certificate_model,
        args.certificate_prime_limit,
        (-2.0, -0.5, 0.5, 2.0),
    )
    total_positivity = prime_log_total_positivity_guard()
    print_report(model_rows, certificate, total_positivity)

    algebra_errors = [
        certificate["two_commutator_response_error"],
        certificate["detector_transport_commutator"],
        certificate["coframe_sonin_orthogonality"],
        certificate["coframe_band_pairing_error"],
    ]
    for model, rows in model_rows:
        algebra_errors.extend(
            [
                model.fourier_unitarity_error,
                model.scattering_unitarity_error,
                model.nesting_error,
            ]
        )
        for row in rows:
            algebra_errors.extend(
                [
                    row["response_at_zero"],
                    row["response_hermitian_error"],
                    row["rank_trace_error"],
                ]
            )

    maximum_error = max(algebra_errors)
    print(f"maximum checked algebra error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )
    if total_positivity["x_order_margin"] <= 0.0:
        raise SystemExit("total-positivity guard x points are not ordered")
    if total_positivity["y_order_margin"] <= 0.0:
        raise SystemExit("total-positivity guard y points are not ordered")
    if total_positivity["ordered_minor"] >= -0.7:
        raise SystemExit("total-positivity guard no longer has a negative minor")


if __name__ == "__main__":
    main()
