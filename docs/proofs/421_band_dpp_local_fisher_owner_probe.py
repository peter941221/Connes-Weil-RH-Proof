#!/usr/bin/env python3
"""Finite certificate for Proof 421's band-DPP local Fisher owner."""

from __future__ import annotations

import argparse
import itertools

import numpy as np


def positive_logdet(matrix: np.ndarray) -> float:
    hermitian = (matrix + matrix.conj().T) / 2.0
    eigenvalues = np.linalg.eigvalsh(hermitian)
    if float(np.min(eigenvalues)) <= 1.0e-13:
        raise ValueError("matrix is not numerically positive definite")
    return float(np.sum(np.log(eigenvalues)))


def projection(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.solve(gram, frame.conj().T)


def fixed_size_subsets(size: int, rank: int) -> list[tuple[int, ...]]:
    return list(itertools.combinations(range(size), rank))


def dpp_probabilities(
    frame: np.ndarray, subsets: list[tuple[int, ...]]
) -> np.ndarray:
    log_weights = []
    for subset in subsets:
        minor = frame[np.asarray(subset), :]
        determinant = np.linalg.det(minor)
        if abs(determinant) <= 1.0e-14:
            raise ValueError("generic frame produced a vanishing DPP minor")
        log_weights.append(2.0 * np.log(abs(determinant)))
    log_weights_array = np.asarray(log_weights)
    maximum = float(np.max(log_weights_array))
    weights = np.exp(log_weights_array - maximum)
    return weights / np.sum(weights)


def subset_statistics(
    values: np.ndarray, subsets: list[tuple[int, ...]]
) -> np.ndarray:
    return np.asarray(
        [float(np.sum(values[np.asarray(subset)])) for subset in subsets]
    )


def expectation(probabilities: np.ndarray, values: np.ndarray) -> float:
    return float(np.dot(probabilities, values))


def variance(probabilities: np.ndarray, values: np.ndarray) -> float:
    mean = expectation(probabilities, values)
    return expectation(probabilities, (values - mean) ** 2)


def covariance(
    probabilities: np.ndarray, left: np.ndarray, right: np.ndarray
) -> float:
    left_centered = left - expectation(probabilities, left)
    right_centered = right - expectation(probabilities, right)
    return expectation(probabilities, left_centered * right_centered)


def kl_divergence(left: np.ndarray, right: np.ndarray) -> float:
    return float(np.dot(left, np.log(left / right)))


def conditional_score(
    probabilities: np.ndarray, statistic: np.ndarray, score: np.ndarray
) -> np.ndarray:
    result = np.zeros_like(score)
    for value in np.unique(statistic):
        mask = statistic == value
        mass = float(np.sum(probabilities[mask]))
        result[mask] = float(np.dot(probabilities[mask], score[mask]) / mass)
    return result


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    raw = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    unitary, triangular = np.linalg.qr(raw)
    phases = np.diag(triangular).copy()
    phases /= np.abs(phases)
    return unitary @ np.diag(np.conjugate(phases))


def scalar_weight_certificate(
    size: int, rank: int, rng: np.random.Generator, quadrature_order: int
) -> dict[str, float]:
    frame = random_unitary(size, rng)[:, :rank]
    subsets = fixed_size_subsets(size, rank)
    source_probabilities = dpp_probabilities(frame, subsets)
    source_projection = projection(frame)

    projection_probabilities = np.asarray(
        [
            float(
                np.linalg.det(
                    source_projection[np.ix_(subset, subset)]
                ).real
            )
            for subset in subsets
        ]
    )

    log_weight = 0.48 * np.sin(np.linspace(-1.1, 2.3, size))
    log_weight += 0.17 * np.cos(np.linspace(-0.7, 3.0, size))
    multiplier = np.exp(log_weight / 2.0)
    moved_frame = multiplier[:, None] * frame
    moved_probabilities = dpp_probabilities(moved_frame, subsets)

    detector = 0.35 * np.cos(np.linspace(-1.5, 2.4, size))
    detector += 0.19 * np.sin(np.linspace(-0.2, 2.8, size))
    detector_statistic = subset_statistics(detector, subsets)
    weight_statistic = subset_statistics(log_weight, subsets)

    tilted_density = np.exp(weight_statistic)
    tilted_density /= expectation(source_probabilities, tilted_density)
    density_probabilities = source_probabilities * tilted_density

    parameter = 0.37
    direct_log_mgf = np.log(
        expectation(moved_probabilities, np.exp(parameter * detector_statistic))
    ) - np.log(
        expectation(source_probabilities, np.exp(parameter * detector_statistic))
    )

    source_gram = frame.conj().T @ frame
    moved_gram = moved_frame.conj().T @ moved_frame
    moved_tilted_gram = moved_frame.conj().T @ (
        np.exp(parameter * detector)[:, None] * moved_frame
    )
    source_tilted_gram = frame.conj().T @ (
        np.exp(parameter * detector)[:, None] * frame
    )
    gram_log_mgf = (
        positive_logdet(moved_tilted_gram)
        - positive_logdet(moved_gram)
        - positive_logdet(source_tilted_gram)
        + positive_logdet(source_gram)
    )

    expected_response = expectation(
        moved_probabilities, detector_statistic
    ) - expectation(source_probabilities, detector_statistic)
    projection_response = float(
        np.trace(
            np.diag(detector)
            @ (projection(moved_frame) - source_projection)
        ).real
    )

    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    times = (nodes + 1.0) / 2.0
    weights = weights / 2.0
    covariance_integral = 0.0
    detector_variance_integral = 0.0
    weight_variance_integral = 0.0
    for time, weight in zip(times, weights, strict=True):
        path_density = np.exp(time * weight_statistic)
        path_probabilities = source_probabilities * path_density
        path_probabilities /= np.sum(path_probabilities)
        covariance_integral += weight * covariance(
            path_probabilities, detector_statistic, weight_statistic
        )
        detector_variance_integral += weight * variance(
            path_probabilities, detector_statistic
        )
        weight_variance_integral += weight * variance(
            path_probabilities, weight_statistic
        )

    jeffreys = kl_divergence(
        moved_probabilities, source_probabilities
    ) + kl_divergence(source_probabilities, moved_probabilities)
    square_bound_slack = (
        detector_variance_integral * jeffreys - expected_response**2
    )

    return {
        "probability_normalization_error": abs(np.sum(source_probabilities) - 1.0),
        "projection_probability_error": float(
            np.max(np.abs(projection_probabilities - source_probabilities))
        ),
        "scalar_density_error": float(
            np.max(np.abs(density_probabilities - moved_probabilities))
        ),
        "gram_log_mgf_error": abs(direct_log_mgf - gram_log_mgf),
        "projection_response_error": abs(expected_response - projection_response),
        "covariance_path_error": abs(covariance_integral - expected_response),
        "jeffreys_path_error": abs(weight_variance_integral - jeffreys),
        "square_bound_slack": square_bound_slack,
        "response_magnitude": abs(expected_response),
        "jeffreys_divergence": jeffreys,
    }


def band_frame_and_derivative(
    base_band: np.ndarray, generator: np.ndarray, time: float
) -> tuple[np.ndarray, np.ndarray]:
    carrier = np.eye(generator.shape[0], dtype=complex) + time * generator
    inverse_adjoint = np.linalg.inv(carrier.conj().T)
    frame = inverse_adjoint @ base_band
    derivative = -inverse_adjoint @ generator.conj().T @ frame
    return frame, derivative


def band_score(
    frame: np.ndarray,
    derivative: np.ndarray,
    subsets: list[tuple[int, ...]],
) -> np.ndarray:
    gram = frame.conj().T @ frame
    gram_derivative = derivative.conj().T @ frame + frame.conj().T @ derivative
    normalization_score = float(
        np.trace(np.linalg.solve(gram, gram_derivative)).real
    )
    scores = []
    for subset in subsets:
        indices = np.asarray(subset)
        minor = frame[indices, :]
        minor_derivative = derivative[indices, :]
        raw_score = 2.0 * float(
            np.trace(np.linalg.solve(minor, minor_derivative)).real
        )
        scores.append(raw_score - normalization_score)
    return np.asarray(scores)


def additive_density_fit_residual(
    source: np.ndarray,
    target: np.ndarray,
    subsets: list[tuple[int, ...]],
    size: int,
) -> float:
    design = np.ones((len(subsets), size + 1), dtype=float)
    for row, subset in enumerate(subsets):
        design[row, 1:] = 0.0
        design[row, 1 + np.asarray(subset)] = 1.0
    log_ratio = np.log(target / source)
    coefficients, _, _, _ = np.linalg.lstsq(design, log_ratio, rcond=None)
    residual = log_ratio - design @ coefficients
    return float(np.sqrt(np.mean(residual**2)))


def band_certificate(
    size: int,
    sonin_rank: int,
    rng: np.random.Generator,
    quadrature_order: int,
) -> dict[str, float]:
    unitary = random_unitary(size, rng)
    sonin = unitary[:, :sonin_rank]
    band = unitary[:, sonin_rank:]
    band_rank = band.shape[1]
    subsets = fixed_size_subsets(size, band_rank)

    raw_generator = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    generator = 0.32 * raw_generator / np.linalg.norm(raw_generator, ord=2)
    endpoint_carrier = np.eye(size, dtype=complex) + generator

    moved_sonin = endpoint_carrier @ sonin
    dual_band = np.linalg.solve(endpoint_carrier.conj().T, band)
    wrong_inverse_band = np.linalg.solve(endpoint_carrier, band)
    complement_error = np.linalg.norm(
        projection(moved_sonin) + projection(dual_band) - np.eye(size), ord=2
    )
    wrong_inverse_gap = np.linalg.norm(
        projection(dual_band) - projection(wrong_inverse_band), ord=2
    )

    source_probabilities = dpp_probabilities(band, subsets)
    endpoint_probabilities = dpp_probabilities(dual_band, subsets)
    nonmultiplicative_residual = additive_density_fit_residual(
        source_probabilities, endpoint_probabilities, subsets, size
    )

    detector = np.zeros(size, dtype=float)
    detector[size // 2 :] = 1.0
    detector_statistic = subset_statistics(detector, subsets)
    endpoint_response = expectation(
        endpoint_probabilities, detector_statistic
    ) - expectation(source_probabilities, detector_statistic)

    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    times = (nodes + 1.0) / 2.0
    weights = weights / 2.0
    covariance_integral = 0.0
    detector_variance_integral = 0.0
    conditional_fisher_integral = 0.0
    full_fisher_integral = 0.0
    maximum_score_mean = 0.0
    maximum_variance_error = 0.0
    maximum_conditional_covariance_error = 0.0

    detector_matrix = np.diag(detector)
    for time, weight in zip(times, weights, strict=True):
        frame, derivative = band_frame_and_derivative(band, generator, time)
        probabilities = dpp_probabilities(frame, subsets)
        score = band_score(frame, derivative, subsets)
        localized_score = conditional_score(
            probabilities, detector_statistic, score
        )

        score_mean = expectation(probabilities, score)
        maximum_score_mean = max(maximum_score_mean, abs(score_mean))
        direct_covariance = covariance(
            probabilities, detector_statistic, score
        )
        localized_covariance = covariance(
            probabilities, detector_statistic, localized_score
        )
        maximum_conditional_covariance_error = max(
            maximum_conditional_covariance_error,
            abs(direct_covariance - localized_covariance),
        )

        path_projection = projection(frame)
        commutator = detector_matrix @ path_projection - path_projection @ detector_matrix
        commutator_variance = 0.5 * np.linalg.norm(commutator, ord="fro") ** 2
        direct_variance = variance(probabilities, detector_statistic)
        maximum_variance_error = max(
            maximum_variance_error,
            abs(direct_variance - commutator_variance),
        )

        covariance_integral += weight * direct_covariance
        detector_variance_integral += weight * direct_variance
        conditional_fisher_integral += weight * variance(
            probabilities, localized_score
        )
        full_fisher_integral += weight * variance(probabilities, score)

    integrated_bound_slack = (
        detector_variance_integral * conditional_fisher_integral
        - endpoint_response**2
    )

    return {
        "inverse_adjoint_complement_error": complement_error,
        "wrong_inverse_projection_gap": wrong_inverse_gap,
        "nonmultiplicative_log_density_residual": nonmultiplicative_residual,
        "band_covariance_path_error": abs(covariance_integral - endpoint_response),
        "score_mean_error": maximum_score_mean,
        "conditional_covariance_error": maximum_conditional_covariance_error,
        "commutator_variance_error": maximum_variance_error,
        "conditional_fisher_contraction_slack": (
            full_fisher_integral - conditional_fisher_integral
        ),
        "integrated_fisher_bound_slack": integrated_bound_slack,
        "band_response_magnitude": abs(endpoint_response),
        "conditional_fisher_action": conditional_fisher_integral,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=9)
    parser.add_argument("--sonin-rank", type=int, default=4)
    parser.add_argument("--seed", type=int, default=421)
    parser.add_argument("--quadrature-order", type=int, default=48)
    parser.add_argument("--tolerance", type=float, default=2.0e-9)
    args = parser.parse_args()

    if not 2 <= args.sonin_rank <= args.size - 2:
        raise SystemExit("sonin-rank must leave at least two band dimensions")
    if args.size > 12:
        raise SystemExit("configuration enumeration requires size <= 12")

    rng = np.random.default_rng(args.seed)
    scalar_checks = scalar_weight_certificate(
        args.size, args.sonin_rank, rng, args.quadrature_order
    )
    band_checks = band_certificate(
        args.size, args.sonin_rank, rng, args.quadrature_order
    )

    print("Proof 421 band-DPP local Fisher certificate")
    print("+------------------------------------------+------------------+")
    print("| scalar-weight check                      | value            |")
    print("+------------------------------------------+------------------+")
    for label, value in scalar_checks.items():
        print(f"| {label:40s} | {value:16.9e} |")
    print("+------------------------------------------+------------------+")
    print("+------------------------------------------+------------------+")
    print("| recombined-band check                    | value            |")
    print("+------------------------------------------+------------------+")
    for label, value in band_checks.items():
        print(f"| {label:40s} | {value:16.9e} |")
    print("+------------------------------------------+------------------+")

    scalar_exact_labels = [
        "probability_normalization_error",
        "projection_probability_error",
        "scalar_density_error",
        "gram_log_mgf_error",
        "projection_response_error",
        "covariance_path_error",
        "jeffreys_path_error",
    ]
    band_exact_labels = [
        "inverse_adjoint_complement_error",
        "band_covariance_path_error",
        "score_mean_error",
        "conditional_covariance_error",
        "commutator_variance_error",
    ]
    maximum_exact_error = max(
        max(scalar_checks[label] for label in scalar_exact_labels),
        max(band_checks[label] for label in band_exact_labels),
    )
    print(f"maximum_exact_error={maximum_exact_error:.12e}")

    if maximum_exact_error > args.tolerance:
        raise SystemExit("band-DPP identity failed")
    if scalar_checks["square_bound_slack"] < -args.tolerance:
        raise SystemExit("scalar Jeffreys bound failed")
    if band_checks["conditional_fisher_contraction_slack"] < -args.tolerance:
        raise SystemExit("conditional Fisher information exceeded full Fisher")
    if band_checks["integrated_fisher_bound_slack"] < -args.tolerance:
        raise SystemExit("integrated local Fisher bound failed")
    if band_checks["wrong_inverse_projection_gap"] <= 1.0e-3:
        raise SystemExit("inverse and inverse-adjoint transports accidentally agree")
    if band_checks["nonmultiplicative_log_density_residual"] <= 1.0e-4:
        raise SystemExit("generic band density accidentally became a scalar tilt")

    print("gram_partition=PROJECTION_DPP_LOG_LAPLACE")
    print("scalar_weight_path=JEFFREYS_SQUARE_GAIN")
    print("actual_band_transport=INVERSE_ADJOINT")
    print("generic_band_scalar_tilt=REJECTED")
    print("detector_pushforward_fisher=POSITIVE_FINITE_OWNER")
    print("continuous_band_fisher_energy_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
