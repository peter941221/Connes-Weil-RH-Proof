#!/usr/bin/env python3
"""Certificate for the first-missing renewal row and prime filtration.

The source layer imports Proofs 266 and 270.  It factors Delta through the
actual missing channels I_rand and I_C, exposes one missing channel in every
nonzero renewal term, and verifies that the survivor row is a coisometry onto
Ran(K).

The probability layer checks the fiberwise Doob decomposition

    (P_j-P_(j-1)) V_S = V_<j (V_j-A_j) A_>j

for truncated geometric local laws.  This is an algebra certificate; it does
not prove the compact-root chirp bound for the resulting source row.
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
    specification = importlib.util.spec_from_file_location(
        module_name, path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_266 = load_probe(
    "266_three_branch_causal_determinant_probe.py",
    "proof_266_for_271",
)
PROOF_270 = load_probe(
    "270_renewal_observability_collapse_probe.py",
    "proof_270_for_271",
)


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def missing_channel_data(
    model: dict[str, np.ndarray], owner: dict[str, np.ndarray]
) -> dict[str, np.ndarray]:
    identity = model["identity"]
    complement = model["C"]
    causal = model["A"]
    band_basis = model["b_basis"]
    identity_band = np.eye(band_basis.shape[1], dtype=complex)

    ambient_frame = causal @ band_basis
    random_gram = identity_band - ambient_frame.conj().T @ ambient_frame
    random_channel = PROOF_270.positive_square_root(random_gram)
    outer_channel = complement @ causal @ band_basis
    missing_channel = np.vstack((random_channel, outer_channel))

    return {
        "I_rand": random_channel,
        "I_C": outer_channel,
        "M": missing_channel,
        "random_gram": random_gram,
        "ambient_identity": identity,
        "Delta": owner["Delta"],
    }


def renewal_row_certificate(
    model: dict[str, np.ndarray],
    maximum_power: int,
    tail_tolerance: float,
) -> tuple[dict[str, float], list[dict[str, float]]]:
    owner = PROOF_270.owner_data(model)
    channels = missing_channel_data(model, owner)
    survivor = owner["K"]
    left = owner["L"]
    gamma = owner["Gamma"]
    delta = owner["Delta"]
    defect = owner["D"]
    numerator = owner["N"]
    missing = channels["M"]
    identity_band = np.eye(gamma.shape[0], dtype=complex)

    inverse_gamma = np.linalg.inv(gamma)
    expected_response = np.trace(numerator @ inverse_gamma)
    expected_projection = survivor @ inverse_gamma @ survivor.conj().T

    j_gram = identity_band.copy()
    right_row_gram = survivor @ survivor.conj().T
    left_row_gram = left @ left.conj().T
    pair_trace = np.trace(left.conj().T @ survivor)
    defect_power = identity_band.copy()
    selected_powers = {
        power
        for power in (0, 1, 2, 4, 8, 16, 32, 64, 128, maximum_power)
        if power <= maximum_power
    }
    rows: list[dict[str, float]] = []

    for renewal_index in range(1, maximum_power + 1):
        first_missing = missing @ defect_power
        j_gram += first_missing.conj().T @ first_missing
        right_leg = survivor @ first_missing.conj().T
        left_leg = left @ first_missing.conj().T
        right_row_gram += right_leg @ right_leg.conj().T
        left_row_gram += left_leg @ left_leg.conj().T
        pair_trace += np.trace(left_leg.conj().T @ right_leg)

        if renewal_index in selected_powers:
            rows.append(
                {
                    "power": float(renewal_index),
                    "J_error": relative_error(j_gram, inverse_gamma),
                    "right_error": relative_error(
                        right_row_gram, expected_projection
                    ),
                    "pair_error": relative_error(
                        pair_trace, expected_response
                    ),
                    "left_norm": float(
                        np.linalg.norm(left_row_gram, ord=2)
                    ),
                }
            )

        defect_power = defect_power @ defect
        if (
            renewal_index >= max(selected_powers)
            and float(np.linalg.norm(defect_power, ord=2))
            <= tail_tolerance
        ):
            break

    checks = {
        "missing channel Gram error": relative_error(
            missing.conj().T @ missing, delta
        ),
        "random plus outer defect error": relative_error(
            channels["I_rand"].conj().T @ channels["I_rand"]
            + channels["I_C"].conj().T @ channels["I_C"],
            delta,
        ),
        "renewal J Gram error": relative_error(j_gram, inverse_gamma),
        "right row projection error": relative_error(
            right_row_gram, expected_projection
        ),
        "right row idempotence error": relative_error(
            right_row_gram @ right_row_gram, right_row_gram
        ),
        "right row self-adjoint error": relative_error(
            right_row_gram.conj().T, right_row_gram
        ),
        "row pairing trace error": relative_error(
            pair_trace, expected_response
        ),
        "right row norm excess": max(
            float(np.linalg.norm(right_row_gram, ord=2)) - 1.0,
            0.0,
        ),
        "left row norm": float(np.linalg.norm(left_row_gram, ord=2)),
        "left row trace": float(np.trace(left_row_gram).real),
        "response magnitude": float(abs(expected_response)),
    }
    return checks, rows


def truncated_geometric_law(
    coefficient: float, maximum_mode: int
) -> tuple[np.ndarray, np.ndarray]:
    modes = np.arange(maximum_mode + 1, dtype=float)
    weights = (1.0 - coefficient) * coefficient**modes
    weights /= float(np.sum(weights))
    return modes, weights


def prime_filtration_certificate(
    primes: tuple[int, ...],
    angles: tuple[float, ...],
    maximum_mode: int,
) -> dict[str, float]:
    if len(primes) != len(angles):
        raise ValueError("primes and angles must have the same length")

    local_modes: list[np.ndarray] = []
    local_weights: list[np.ndarray] = []
    local_values: list[np.ndarray] = []
    local_means: list[complex] = []
    for prime, angle in zip(primes, angles):
        modes, weights = truncated_geometric_law(
            prime**-0.5, maximum_mode
        )
        values = np.exp(1j * modes * angle)
        local_modes.append(modes)
        local_weights.append(weights)
        local_values.append(values)
        local_means.append(complex(np.sum(weights * values)))

    outcomes = list(
        itertools.product(range(maximum_mode + 1), repeat=len(primes))
    )
    full_mean = complex(np.prod(local_means))
    variance_sum = 0.0
    full_variance = 0.0
    maximum_formula_error = 0.0
    maximum_cross_inner_product = 0.0

    differences: list[list[complex]] = [
        [] for _ in range(len(primes))
    ]
    outcome_weights: list[float] = []
    full_values: list[complex] = []

    for outcome in outcomes:
        weight = float(
            np.prod(
                [
                    local_weights[index][mode]
                    for index, mode in enumerate(outcome)
                ]
            )
        )
        values = [
            local_values[index][mode]
            for index, mode in enumerate(outcome)
        ]
        full_value = complex(np.prod(values))
        outcome_weights.append(weight)
        full_values.append(full_value)

        for index in range(len(primes)):
            prefix = complex(np.prod(values[:index])) if index else 1.0
            suffix_mean = (
                complex(np.prod(local_means[index + 1 :]))
                if index + 1 < len(primes)
                else 1.0
            )
            formula = (
                prefix
                * (values[index] - local_means[index])
                * suffix_mean
            )
            conditional_current = (
                complex(np.prod(values[: index + 1])) * suffix_mean
            )
            previous_suffix = complex(
                np.prod(local_means[index:])
            )
            conditional_previous = prefix * previous_suffix
            direct = conditional_current - conditional_previous
            maximum_formula_error = max(
                maximum_formula_error, abs(formula - direct)
            )
            differences[index].append(formula)

    weights_array = np.asarray(outcome_weights)
    full_array = np.asarray(full_values)
    full_variance = float(
        np.sum(weights_array * np.abs(full_array - full_mean) ** 2)
    )
    for index, difference_values in enumerate(differences):
        difference = np.asarray(difference_values)
        variance_sum += float(
            np.sum(weights_array * np.abs(difference) ** 2)
        )
        for other_index in range(index):
            other = np.asarray(differences[other_index])
            inner = np.sum(weights_array * np.conj(other) * difference)
            maximum_cross_inner_product = max(
                maximum_cross_inner_product, abs(complex(inner))
            )

    return {
        "local martingale formula error": maximum_formula_error,
        "orthogonal difference inner product": maximum_cross_inner_product,
        "variance decomposition error": abs(variance_sum - full_variance),
        "full variance formula error": abs(
            full_variance - (1.0 - abs(full_mean) ** 2)
        ),
        "full variance": full_variance,
        "sum of prime difference variances": variance_sum,
    }


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------------+---------------+")
    print("| check                                      | value         |")
    print("+--------------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>13.6e} |")
    print("+--------------------------------------------+---------------+")


def print_convergence(rows: list[dict[str, float]]) -> None:
    print("First-missing row convergence")
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )
    print(
        "| power  | J error       | right error   | pair error    | left norm     |"
    )
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['power']):>6d} |"
            f" {row['J_error']:>13.6e} |"
            f" {row['right_error']:>13.6e} |"
            f" {row['pair_error']:>13.6e} |"
            f" {row['left_norm']:>13.6e} |"
        )
    print(
        "+--------+---------------+---------------+---------------+---------------+"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=8)
    parser.add_argument("--seed", type=int, default=271)
    parser.add_argument("--maximum-power", type=int, default=10_000)
    parser.add_argument("--tail-tolerance", type=float, default=1e-14)
    parser.add_argument("--maximum-mode", type=int, default=5)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    model = PROOF_266.build_model(args.multiplicity, args.seed)
    source, convergence = renewal_row_certificate(
        model, args.maximum_power, args.tail_tolerance
    )
    filtration = prime_filtration_certificate(
        (2, 3, 5),
        (0.37, 0.71, 1.13),
        args.maximum_mode,
    )

    print("identity=first-missing renewal row with prime filtration")
    print("status=exact fixed-S and probability algebra; source estimate open")
    print_checks("Source first-missing row", source)
    print()
    print_convergence(convergence)
    print()
    print_checks("Prime Doob filtration", filtration)

    exact_errors = [
        source["missing channel Gram error"],
        source["random plus outer defect error"],
        source["renewal J Gram error"],
        source["right row projection error"],
        source["right row idempotence error"],
        source["right row self-adjoint error"],
        source["row pairing trace error"],
        source["right row norm excess"],
        filtration["local martingale formula error"],
        filtration["orthogonal difference inner product"],
        filtration["variance decomposition error"],
        filtration["full variance formula error"],
    ]
    maximum_error = max(exact_errors)
    print(f"maximum exact error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"first-missing certificate failed: {maximum_error:.6e}"
        )

    print("missing_channel_Gram_verdict=EXACT")
    print("right_survivor_row_verdict=COISOMETRY_ON_RANGE")
    print("prime_Doob_difference_verdict=EXACT")
    print("positive_predictable_h1_bound=REJECTED_BY_PROOF_273")
    print("signed_scalar_local_coefficient=p^(-m/2)")
    print("complete_signed_extra_half_power=OPEN")
    print("signed_paired_source_disintegration=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
