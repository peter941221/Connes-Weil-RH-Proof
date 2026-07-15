#!/usr/bin/env python3
"""Certificate for Proof 286's first-missing relative-mode disintegration.

The source layer factors every nonzero support-first renewal term through the
actual random and outer missing channels.  The probability layer then checks
that a Doob prime channel loses its common unitary past inside the completed
scalar trace and becomes an exact second difference indexed by the relative
geometric mode.  The predictable future average remains inside the scalar.
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import math
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


PROOF_285 = load_probe(
    "285_support_first_boundary_renewal_probe.py",
    "proof_285_for_286",
)
PROOF_270 = PROOF_285.PROOF_270
PROOF_266 = PROOF_285.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def source_missing_channel_certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    maximum_power: int,
    tail_tolerance: float,
) -> tuple[dict[str, float | complex], np.ndarray]:
    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 31
    )

    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    causal = model["A"]
    band_basis = model["b_basis"]
    survivor = outer @ causal @ band_basis
    gamma = survivor.conj().T @ survivor
    inverse_gamma = np.linalg.inv(gamma)
    identity_band = np.eye(gamma.shape[0], dtype=complex)
    delta = identity_band - gamma

    ambient_frame = causal @ band_basis
    random_gram = identity_band - ambient_frame.conj().T @ ambient_frame
    random_channel = PROOF_270.positive_square_root(random_gram)
    outer_channel = complement @ causal @ band_basis
    channel_gram = (
        random_channel.conj().T @ random_channel
        + outer_channel.conj().T @ outer_channel
    )

    detector_band = band_basis.conj().T @ detector @ band_basis
    numerator = (
        survivor.conj().T @ detector @ survivor
        - detector_band @ gamma
    )
    endpoint_response = np.trace(numerator @ inverse_gamma)

    base_boundary = (
        sonin @ causal.conj().T @ survivor @ band_basis.conj().T
        - survivor
        @ band_basis.conj().T
        @ causal.conj().T
        @ complement
    )
    base_response = np.trace(detector @ base_boundary)
    reconstructed_response = base_response
    random_response = 0.0j
    outer_response = 0.0j
    maximum_level_error = 0.0
    channel_absolute_mass = 0.0
    power = identity_band.copy()
    route_operator = np.zeros_like(model["identity"])

    for renewal_index in range(1, maximum_power + 1):
        boundary_reward = (
            band_basis.conj().T
            @ detector
            @ sonin
            @ causal.conj().T
            @ survivor
            @ power
            - band_basis.conj().T
            @ causal.conj().T
            @ complement
            @ detector
            @ survivor
            @ power
        )
        random_level = np.trace(
            random_channel @ boundary_reward @ random_channel.conj().T
        )
        outer_level = np.trace(
            outer_channel @ boundary_reward @ outer_channel.conj().T
        )
        channel_level = random_level + outer_level

        next_power = power @ delta
        direct_boundary = (
            sonin
            @ causal.conj().T
            @ survivor
            @ next_power
            @ band_basis.conj().T
            - survivor
            @ next_power
            @ band_basis.conj().T
            @ causal.conj().T
            @ complement
        )
        direct_level = np.trace(detector @ direct_boundary)
        maximum_level_error = max(
            maximum_level_error, abs(channel_level - direct_level)
        )
        reconstructed_response += channel_level
        random_response += random_level
        outer_response += outer_level
        channel_absolute_mass += abs(random_level) + abs(outer_level)

        if renewal_index == 1:
            route_operator = (
                band_basis @ boundary_reward @ band_basis.conj().T
            )
        power = next_power
        if (
            renewal_index >= 8
            and float(np.linalg.norm(power, ord=2)) <= tail_tolerance
        ):
            break

    response_scale = max(abs(endpoint_response), 1e-15)
    return {
        "missing channel Gram error": relative_error(channel_gram, delta),
        "base boundary response error": relative_error(
            base_response, np.trace(numerator)
        ),
        "maximum missing-channel level error": maximum_level_error,
        "reconstructed endpoint error": relative_error(
            reconstructed_response, endpoint_response
        ),
        "channel absolute cancellation ratio": float(
            channel_absolute_mass / response_scale
        ),
        "random missing response magnitude": float(abs(random_response)),
        "outer missing response magnitude": float(abs(outer_response)),
        "endpoint response magnitude": float(abs(endpoint_response)),
        "terminal renewal-power norm": float(np.linalg.norm(power, ord=2)),
        "endpoint response": complex(endpoint_response),
    }, route_operator


def geometric_law(
    prime: int, maximum_mode: int
) -> tuple[np.ndarray, np.ndarray]:
    modes = np.arange(maximum_mode + 1, dtype=int)
    coefficient = prime**-0.5
    weights = (1.0 - coefficient) * coefficient**modes
    weights /= float(np.sum(weights))
    return modes, weights


def translation_family(size: int, seed: int):
    rng = np.random.default_rng(seed)
    random_matrix = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    basis, _ = np.linalg.qr(random_matrix)
    spectrum = np.linspace(-1.1, 1.3, size)

    def translation(displacement: float) -> np.ndarray:
        phases = np.exp(1j * displacement * spectrum)
        return basis @ np.diag(phases) @ basis.conj().T

    return translation


def probability_relative_mode_certificate(
    route_operator: np.ndarray,
    primes: tuple[int, ...],
    selected_index: int,
    maximum_mode: int,
    seed: int,
) -> dict[str, float | complex]:
    size = route_operator.shape[0]
    translation = translation_family(size, seed + 101)
    local_modes: list[np.ndarray] = []
    local_weights: list[np.ndarray] = []
    local_translations: list[list[np.ndarray]] = []
    local_averages: list[np.ndarray] = []

    for prime in primes:
        modes, weights = geometric_law(prime, maximum_mode)
        operators = [
            translation(float(mode) * math.log(prime)) for mode in modes
        ]
        average = sum(
            weight * operator
            for weight, operator in zip(weights, operators)
        )
        local_modes.append(modes)
        local_weights.append(weights)
        local_translations.append(operators)
        local_averages.append(average)

    future_average = np.eye(size, dtype=complex)
    for average in local_averages[selected_index + 1 :]:
        future_average = future_average @ average

    selected_average = local_averages[selected_index]
    selected_operators = local_translations[selected_index]
    selected_weights = local_weights[selected_index]
    future_reward = (
        future_average
        @ route_operator
        @ future_average.conj().T
    )

    direct_with_past = 0.0j
    prefix_ranges = [
        range(len(local_modes[index])) for index in range(selected_index)
    ]
    prefix_outcomes = (
        itertools.product(*prefix_ranges) if prefix_ranges else [()]
    )
    for prefix_outcome in prefix_outcomes:
        prefix_weight = 1.0
        prefix_unitary = np.eye(size, dtype=complex)
        for index, mode_index in enumerate(prefix_outcome):
            prefix_weight *= float(local_weights[index][mode_index])
            prefix_unitary = (
                prefix_unitary @ local_translations[index][mode_index]
            )
        for weight, operator in zip(selected_weights, selected_operators):
            innovation = operator - selected_average
            doob_channel = (
                prefix_unitary @ innovation @ future_average
            )
            direct_with_past += prefix_weight * float(weight) * np.trace(
                doob_channel
                @ route_operator
                @ doob_channel.conj().T
            )

    no_past = 0.0j
    for weight, operator in zip(selected_weights, selected_operators):
        innovation = operator - selected_average
        no_past += float(weight) * np.trace(
            innovation @ future_reward @ innovation.conj().T
        )

    centered_covariance = np.trace(future_reward)
    centered_covariance -= np.trace(
        selected_average
        @ future_reward
        @ selected_average.conj().T
    )

    double_difference = 0.0j
    grouped_difference = 0.0j
    relative_probabilities: dict[int, float] = {}
    for left_index, (left_weight, left_operator) in enumerate(
        zip(selected_weights, selected_operators)
    ):
        for right_index, (right_weight, right_operator) in enumerate(
            zip(selected_weights, selected_operators)
        ):
            pair_weight = float(left_weight * right_weight)
            difference = left_operator - right_operator
            double_difference += 0.5 * pair_weight * np.trace(
                difference @ future_reward @ difference.conj().T
            )
            relative_mode = left_index - right_index
            relative_probabilities[relative_mode] = (
                relative_probabilities.get(relative_mode, 0.0)
                + pair_weight
            )

    selected_prime = primes[selected_index]
    for relative_mode, probability in relative_probabilities.items():
        relative_translation = translation(
            float(relative_mode) * math.log(selected_prime)
        )
        difference = relative_translation - np.eye(size, dtype=complex)
        grouped_difference += 0.5 * probability * np.trace(
            difference @ future_reward @ difference.conj().T
        )

    wrong_without_future = 0.0j
    for weight, operator in zip(selected_weights, selected_operators):
        innovation = operator - selected_average
        wrong_without_future += float(weight) * np.trace(
            innovation @ route_operator @ innovation.conj().T
        )

    coefficient = selected_prime**-0.5
    infinite_first_mode = (1.0 - coefficient) / (
        1.0 + coefficient
    ) * coefficient
    truncated_first_mode = relative_probabilities.get(1, 0.0)
    return {
        "common past cancellation error": relative_error(
            direct_with_past, no_past
        ),
        "centered covariance error": relative_error(
            centered_covariance, no_past
        ),
        "double-difference error": relative_error(
            double_difference, no_past
        ),
        "relative-mode grouping error": relative_error(
            grouped_difference, no_past
        ),
        "relative probability normalization error": abs(
            sum(relative_probabilities.values()) - 1.0
        ),
        "future-average deletion gap": float(
            abs(wrong_without_future - no_past)
        ),
        "relative-mode absolute ratio": float(
            sum(
                0.5
                * probability
                * abs(
                    np.trace(
                        (
                            translation(
                                float(relative_mode)
                                * math.log(selected_prime)
                            )
                            - np.eye(size, dtype=complex)
                        )
                        @ future_reward
                        @ (
                            translation(
                                float(relative_mode)
                                * math.log(selected_prime)
                            )
                            - np.eye(size, dtype=complex)
                        ).conj().T
                    )
                )
                for relative_mode, probability in relative_probabilities.items()
            )
            / max(abs(no_past), 1e-15)
        ),
        "truncated first relative-mode probability": float(
            truncated_first_mode
        ),
        "infinite geometric first-mode coefficient": float(
            infinite_first_mode
        ),
        "first-mode truncation error": float(
            abs(truncated_first_mode - infinite_first_mode)
        ),
        "relative scalar": complex(no_past),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=286)
    parser.add_argument("--maximum-power", type=int, default=10_000)
    parser.add_argument("--tail-tolerance", type=float, default=1e-14)
    parser.add_argument("--maximum-mode", type=int, default=8)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--guard-floor", type=float, default=1e-5)
    args = parser.parse_args()

    source, route_operator = source_missing_channel_certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.maximum_power,
        args.tail_tolerance,
    )
    probability = probability_relative_mode_certificate(
        route_operator,
        (2, 3, 5, 7),
        2,
        args.maximum_mode,
        args.seed,
    )

    print("identity=first-missing relative-mode scalar disintegration")
    print("status=exact fixed-S channel and probability algebra")
    for title, checks in (
        ("source", source),
        ("probability", probability),
    ):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            if isinstance(value, complex):
                print(f"{label.replace(' ', '_')}_real={value.real:.12e}")
                print(f"{label.replace(' ', '_')}_imag={value.imag:.12e}")
            else:
                print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_errors = (
        float(source["missing channel Gram error"]),
        float(source["base boundary response error"]),
        float(source["maximum missing-channel level error"]),
        float(source["reconstructed endpoint error"]),
        max(
            float(source["terminal renewal-power norm"])
            - args.tail_tolerance,
            0.0,
        ),
        float(probability["common past cancellation error"]),
        float(probability["centered covariance error"]),
        float(probability["double-difference error"]),
        float(probability["relative-mode grouping error"]),
        float(probability["relative probability normalization error"]),
    )
    maximum_exact_error = max(exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "first-missing relative-mode certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if float(probability["future-average deletion gap"]) < args.guard_floor:
        raise SystemExit("predictable future average unexpectedly disappeared")

    print("support_first_missing_channel_factorization=EXACT")
    print("random_plus_outer_missing_channels=EXACT")
    print("common_past_translation_history=ELIMINATED")
    print("local_centered_covariance=RELATIVE_MODE_SECOND_DIFFERENCE")
    print("predictable_future_average=MANDATORY")
    print("relative_geometric_coefficient=ONE_COPY_a^abs_r")
    print("continuous_source_kernel_readback=OPEN")
    print("complete_signed_extra_half_power=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
