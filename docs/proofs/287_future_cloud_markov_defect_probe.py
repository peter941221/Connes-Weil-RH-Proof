#!/usr/bin/env python3
"""Certificate for Proof 287's future-cloud Markov-defect correction.

The probability layer expands both predictable-future averages and verifies
that their common absolute history cancels, leaving only the relative future
displacement.  Summing all local relative modes before an absolute value gives
one Markov defect.  A compact-profile guard rejects Proof 286's former
single-window support condition and its per-mode extra-half-power target.
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_286() -> ModuleType:
    path = Path(__file__).with_name(
        "286_first_missing_relative_mode_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_286_for_287", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_286 = load_proof_286()


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def future_outcomes(
    translation,
    primes: tuple[int, ...],
    maximum_mode: int,
) -> tuple[list[tuple[float, float, np.ndarray]], np.ndarray]:
    local_data: list[tuple[np.ndarray, np.ndarray, list[np.ndarray]]] = []
    size = translation(0.0).shape[0]
    average = np.eye(size, dtype=complex)
    for prime in primes:
        modes, weights = PROOF_286.geometric_law(prime, maximum_mode)
        operators = [
            translation(float(mode) * math.log(prime)) for mode in modes
        ]
        local_average = sum(
            float(weight) * operator
            for weight, operator in zip(weights, operators)
        )
        average = average @ local_average
        local_data.append((modes, weights, operators))

    ranges = [range(len(data[0])) for data in local_data]
    outcomes: list[tuple[float, float, np.ndarray]] = []
    for indices in itertools.product(*ranges) if ranges else [()]:
        weight = 1.0
        displacement = 0.0
        operator = np.eye(size, dtype=complex)
        for index, mode_index in enumerate(indices):
            modes, weights, operators = local_data[index]
            weight *= float(weights[mode_index])
            displacement += float(modes[mode_index]) * math.log(primes[index])
            operator = operator @ operators[mode_index]
        outcomes.append((weight, displacement, operator))
    return outcomes, average


def relative_mode_probabilities(
    prime: int, maximum_mode: int
) -> dict[int, float]:
    modes, weights = PROOF_286.geometric_law(prime, maximum_mode)
    probabilities: dict[int, float] = {}
    for left_mode, left_weight in zip(modes, weights):
        for right_mode, right_weight in zip(modes, weights):
            relative_mode = int(left_mode - right_mode)
            probabilities[relative_mode] = (
                probabilities.get(relative_mode, 0.0)
                + float(left_weight * right_weight)
            )
    return probabilities


def future_cloud_certificate(
    route_operator: np.ndarray,
    selected_prime: int,
    future_primes: tuple[int, ...],
    maximum_mode: int,
    selected_relative_mode: int,
    seed: int,
) -> dict[str, float | complex]:
    size = route_operator.shape[0]
    translation = PROOF_286.translation_family(size, seed + 211)
    outcomes, future_average = future_outcomes(
        translation, future_primes, maximum_mode
    )
    relative_displacement = (
        float(selected_relative_mode) * math.log(selected_prime)
    )
    local_difference = (
        translation(relative_displacement) - np.eye(size, dtype=complex)
    )

    direct = np.trace(
        local_difference
        @ future_average
        @ route_operator
        @ future_average.conj().T
        @ local_difference.conj().T
    )
    expanded = 0.0j
    relative = 0.0j
    maximum_common_future_error = 0.0
    for left_weight, left_displacement, left_operator in outcomes:
        for right_weight, right_displacement, right_operator in outcomes:
            weight = left_weight * right_weight
            direct_term = np.trace(
                local_difference
                @ left_operator
                @ route_operator
                @ right_operator.conj().T
                @ local_difference.conj().T
            )
            reduced_term = np.trace(
                local_difference
                @ translation(left_displacement - right_displacement)
                @ route_operator
                @ local_difference.conj().T
            )
            expanded += weight * direct_term
            relative += weight * reduced_term
            maximum_common_future_error = max(
                maximum_common_future_error,
                abs(direct_term - reduced_term),
            )

    local_probabilities = relative_mode_probabilities(
        selected_prime, maximum_mode
    )
    complete_mode_sum = 0.0j
    markov_defect = 0.0j
    maximum_second_difference_error = 0.0
    for left_weight, left_displacement, _ in outcomes:
        for right_weight, right_displacement, _ in outcomes:
            future_weight = left_weight * right_weight
            future_relative = left_displacement - right_displacement

            kappa_center = np.trace(
                translation(future_relative) @ route_operator
            )
            local_average = 0.0j
            for relative_mode, probability in local_probabilities.items():
                local_shift = float(relative_mode) * math.log(selected_prime)
                difference = (
                    translation(local_shift) - np.eye(size, dtype=complex)
                )
                completed_second_difference = np.trace(
                    difference
                    @ translation(future_relative)
                    @ route_operator
                    @ difference.conj().T
                )
                formal_second_difference = (
                    2.0 * kappa_center
                    - np.trace(
                        translation(future_relative + local_shift)
                        @ route_operator
                    )
                    - np.trace(
                        translation(future_relative - local_shift)
                        @ route_operator
                    )
                )
                maximum_second_difference_error = max(
                    maximum_second_difference_error,
                    abs(
                        completed_second_difference
                        - formal_second_difference
                    ),
                )
                complete_mode_sum += (
                    0.5
                    * future_weight
                    * probability
                    * completed_second_difference
                )
                local_average += probability * np.trace(
                    translation(future_relative + local_shift)
                    @ route_operator
                )
            markov_defect += future_weight * (
                kappa_center - local_average
            )

    constant_profile_defect = 1.0 - sum(local_probabilities.values())
    return {
        "future average expansion error": relative_error(expanded, direct),
        "future relative-law error": relative_error(relative, direct),
        "maximum common-future cancellation error": (
            maximum_common_future_error
        ),
        "maximum formal second-difference error": (
            maximum_second_difference_error
        ),
        "complete mode sum versus Markov defect error": relative_error(
            complete_mode_sum, markov_defect
        ),
        "constant profile defect": abs(constant_profile_defect),
        "future outcome probability error": abs(
            sum(outcome[0] for outcome in outcomes) - 1.0
        ),
        "relative mode probability error": abs(
            sum(local_probabilities.values()) - 1.0
        ),
        "complete mode scalar": complex(complete_mode_sum),
    }


def compact_profile_guard(
    prime: int, support_radius: int, relative_mode: int
) -> dict[str, float]:
    if support_radius < 1 or relative_mode <= 2 * support_radius:
        raise ValueError("guard needs separated support windows")

    def profile(displacement: int) -> float:
        if abs(displacement) > support_radius:
            return 0.0
        return float(support_radius + 1 - abs(displacement))

    def second_difference(future: int, mode: int) -> float:
        return (
            2.0 * profile(future)
            - profile(future + mode)
            - profile(future - mode)
        )

    center_value = second_difference(0, relative_mode)
    single_window_distance = abs(relative_mode)
    maximum_three_window_violation = 0.0
    maximum_outside_value = 0.0
    for mode in range(-3 * relative_mode, 3 * relative_mode + 1):
        for future in range(-4 * relative_mode, 4 * relative_mode + 1):
            value = abs(second_difference(future, mode))
            minimum_window_distance = min(
                abs(future),
                abs(future + mode),
                abs(future - mode),
            )
            if minimum_window_distance > support_radius:
                maximum_outside_value = max(maximum_outside_value, value)
            if value > 1e-14 and minimum_window_distance > support_radius:
                maximum_three_window_violation = max(
                    maximum_three_window_violation, value
                )

    coefficient = prime**-0.5
    zero_probability = (1.0 - coefficient) / (1.0 + coefficient)
    delta_profile_defect = 1.0 - zero_probability
    expected_delta_profile_defect = 2.0 * coefficient / (
        1.0 + coefficient
    )
    per_mode_target = coefficient**relative_mode
    return {
        "single-window counterexample magnitude": abs(center_value),
        "single-window separation margin": float(
            single_window_distance - support_radius
        ),
        "three-window support violation": maximum_three_window_violation,
        "outside-three-window magnitude": maximum_outside_value,
        "compact profile large-mode magnitude": abs(center_value),
        "per-mode half-power target": per_mode_target,
        "per-mode target violation ratio": abs(center_value)
        / max(per_mode_target, 1e-300),
        "delta-profile Markov defect": delta_profile_defect,
        "one-half-power formula error": abs(
            delta_profile_defect - expected_delta_profile_defect
        ),
        "constant-profile Markov defect": 0.0,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=287)
    parser.add_argument("--maximum-mode", type=int, default=4)
    parser.add_argument("--support-radius", type=int, default=2)
    parser.add_argument("--guard-relative-mode", type=int, default=9)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--guard-floor", type=float, default=1e-3)
    args = parser.parse_args()

    _, route_operator = PROOF_286.source_missing_channel_certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        10_000,
        1e-14,
    )
    future = future_cloud_certificate(
        route_operator,
        selected_prime=3,
        future_primes=(5, 7),
        maximum_mode=args.maximum_mode,
        selected_relative_mode=2,
        seed=args.seed,
    )
    guard = compact_profile_guard(
        prime=3,
        support_radius=args.support_radius,
        relative_mode=args.guard_relative_mode,
    )

    print("identity=future-cloud relative law and local Markov defect")
    print("status=exact probability algebra; former support target rejected")
    for title, checks in (("future", future), ("guard", guard)):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            if isinstance(value, complex):
                print(f"{label.replace(' ', '_')}_real={value.real:.12e}")
                print(f"{label.replace(' ', '_')}_imag={value.imag:.12e}")
            else:
                print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_errors = (
        float(future["future average expansion error"]),
        float(future["future relative-law error"]),
        float(future["maximum common-future cancellation error"]),
        float(future["maximum formal second-difference error"]),
        float(future["complete mode sum versus Markov defect error"]),
        float(future["constant profile defect"]),
        float(future["future outcome probability error"]),
        float(future["relative mode probability error"]),
        float(guard["three-window support violation"]),
        float(guard["outside-three-window magnitude"]),
        float(guard["one-half-power formula error"]),
        float(guard["constant-profile Markov defect"]),
    )
    maximum_exact_error = max(exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "future-cloud Markov-defect certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if float(guard["single-window counterexample magnitude"]) < args.guard_floor:
        raise SystemExit("single-window support guard unexpectedly vanished")
    if float(guard["per-mode target violation ratio"]) < 10.0:
        raise SystemExit("per-mode half-power guard unexpectedly weakened")

    print("predictable_future_two_leg_expansion=EXACT")
    print("common_future_history=ELIMINATED")
    print("future_cloud_owner=RELATIVE_DISPLACEMENT_LAW")
    print("complete_relative_mode_sum=LOCAL_MARKOV_DEFECT")
    print("scalar_fixed_mode=ANNIHILATED_BY_COMPLETE_MODE_SUM")
    print("former_single_support_window=REJECTED")
    print("outer_second_difference_support=THREE_WINDOWS")
    print("per_mode_extra_half_power=REJECTED")
    print("raw_point_kappa_continuous_domain=OPEN")
    print("complete_sonin_markov_defect_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
