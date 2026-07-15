#!/usr/bin/env python3
"""Certificate for Proof 288's completed Markov trace-domain collapse.

The source-shaped layer rewrites the ambient reward through the two detector
commutators.  The probability layer identifies the relative geometric Markov
operator with A_p A_p* and checks that the displacement-coefficient defect,
the completed second-difference sum, and one operator defect are identical.
"""

from __future__ import annotations

import argparse
import importlib.util
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


PROOF_286 = load_probe(
    "286_first_missing_relative_mode_probe.py",
    "proof_286_for_288",
)
PROOF_285 = PROOF_286.PROOF_285
PROOF_270 = PROOF_286.PROOF_270
PROOF_266 = PROOF_286.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def trace_norm(operator: np.ndarray) -> float:
    return float(np.sum(np.linalg.svd(operator, compute_uv=False)))


def completed_reward_certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    renewal_power: int,
) -> tuple[dict[str, float], np.ndarray]:
    if renewal_power < 0:
        raise ValueError("renewal power must be nonnegative")
    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 31
    )

    complement = model["C"]
    outer = model["E"]
    sonin = model["R"]
    band = model["B"]
    causal = model["A"]
    band_basis = model["b_basis"]
    survivor = outer @ causal @ band_basis
    gamma = survivor.conj().T @ survivor
    identity_band = np.eye(gamma.shape[0], dtype=complex)
    delta = identity_band - gamma
    power = np.linalg.matrix_power(delta, renewal_power)

    reward_on_band = (
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
    ambient_reward = band_basis @ reward_on_band @ band_basis.conj().T

    detector_sonin = PROOF_266.commutator(detector, sonin)
    detector_outer = PROOF_266.commutator(detector, outer)
    sonin_commutator_branch = (
        band
        @ detector_sonin
        @ sonin
        @ causal.conj().T
        @ survivor
        @ power
        @ band_basis.conj().T
    )
    outer_commutator_branch = (
        -band
        @ causal.conj().T
        @ complement
        @ detector_outer
        @ survivor
        @ power
        @ band_basis.conj().T
    )
    commutator_reward = sonin_commutator_branch + outer_commutator_branch

    complete_norm = trace_norm(ambient_reward)
    branch_norm_sum = trace_norm(sonin_commutator_branch) + trace_norm(
        outer_commutator_branch
    )
    copies = 8
    direct_sum_reward = np.kron(
        np.eye(copies, dtype=complex), ambient_reward
    )
    return {
        "ambient reward commutator factorization error": relative_error(
            ambient_reward, commutator_reward
        ),
        "Sonin commutator reconstruction error": relative_error(
            band @ detector @ sonin,
            band @ detector_sonin @ sonin,
        ),
        "outer commutator reconstruction error": relative_error(
            complement @ detector @ survivor,
            complement @ detector_outer @ survivor,
        ),
        "complete reward trace norm": complete_norm,
        "branch trace-norm triangle ratio": branch_norm_sum
        / max(complete_norm, 1e-15),
        "direct-sum trace-norm scaling error": relative_error(
            trace_norm(direct_sum_reward), copies * complete_norm
        ),
        "direct-sum trace-norm growth": trace_norm(direct_sum_reward)
        / max(complete_norm, 1e-15),
    }, ambient_reward


def markov_trace_certificate(
    reward: np.ndarray,
    prime: int,
    maximum_mode: int,
    seed: int,
) -> dict[str, float | complex]:
    size = reward.shape[0]
    translation = PROOF_286.translation_family(size, seed + 301)
    modes, weights = PROOF_286.geometric_law(prime, maximum_mode)
    local_operators = [
        translation(float(mode) * math.log(prime)) for mode in modes
    ]
    local_average = sum(
        float(weight) * operator
        for weight, operator in zip(weights, local_operators)
    )
    relative_probabilities: dict[int, float] = {}
    for left_mode, left_weight in zip(modes, weights):
        for right_mode, right_weight in zip(modes, weights):
            relative_mode = int(left_mode - right_mode)
            relative_probabilities[relative_mode] = (
                relative_probabilities.get(relative_mode, 0.0)
                + float(left_weight * right_weight)
            )

    relative_markov = sum(
        probability
        * translation(float(relative_mode) * math.log(prime))
        for relative_mode, probability in relative_probabilities.items()
    )
    gram_markov = local_average @ local_average.conj().T
    defect = np.eye(size, dtype=complex) - relative_markov

    maximum_point_defect_error = 0.0
    maximum_second_difference_error = 0.0
    selected_defect = 0.0j
    for displacement in (-2.3, -0.7, 0.0, 0.9, 2.8):
        translated_reward = translation(displacement) @ reward
        kappa = np.trace(translated_reward)
        averaged_kappa = 0.0j
        completed_sum = 0.0j
        for relative_mode, probability in relative_probabilities.items():
            local_shift = float(relative_mode) * math.log(prime)
            shifted_kappa = np.trace(
                translation(displacement + local_shift) @ reward
            )
            averaged_kappa += probability * shifted_kappa
            local_difference = (
                translation(local_shift) - np.eye(size, dtype=complex)
            )
            completed_sum += 0.5 * probability * np.trace(
                local_difference
                @ translated_reward
                @ local_difference.conj().T
            )
        point_defect = kappa - averaged_kappa
        operator_defect = np.trace(
            translation(displacement) @ defect @ reward
        )
        maximum_point_defect_error = max(
            maximum_point_defect_error,
            abs(point_defect - operator_defect),
        )
        maximum_second_difference_error = max(
            maximum_second_difference_error,
            abs(completed_sum - operator_defect),
        )
        if displacement == 0.0:
            selected_defect = operator_defect

    return {
        "relative Markov versus local Gram error": relative_error(
            relative_markov, gram_markov
        ),
        "relative probability normalization error": abs(
            sum(relative_probabilities.values()) - 1.0
        ),
        "maximum point Markov-defect error": maximum_point_defect_error,
        "maximum completed second-difference error": (
            maximum_second_difference_error
        ),
        "defect self-adjoint error": relative_error(
            defect, defect.conj().T
        ),
        "defect minimum eigenvalue violation": max(
            -float(np.min(np.linalg.eigvalsh(defect))), 0.0
        ),
        "selected defect scalar": complex(selected_defect),
    }


def exact_geometric_defect_certificate(
    prime: int, spectral_size: int
) -> dict[str, float]:
    if spectral_size < 4:
        raise ValueError("spectral size must be at least four")
    coefficient = prime**-0.5
    angles = np.linspace(0.0, 2.0 * math.pi, spectral_size, endpoint=False)
    if not np.any(np.isclose(angles, math.pi)):
        angles = np.append(angles, math.pi)
    unitary = np.diag(np.exp(1j * angles))
    identity = np.eye(unitary.shape[0], dtype=complex)
    local_average = (1.0 - coefficient) * np.linalg.inv(
        identity - coefficient * unitary
    )
    defect = identity - local_average @ local_average.conj().T
    expected_norm = 4.0 * coefficient / (1.0 + coefficient) ** 2
    return {
        "exact geometric average fixed-mode error": float(
            np.linalg.norm(local_average[0, 0] - 1.0)
        ),
        "exact defect positivity violation": max(
            -float(np.min(np.linalg.eigvalsh(defect))), 0.0
        ),
        "exact defect norm formula error": abs(
            float(np.linalg.norm(defect, ord=2)) - expected_norm
        ),
        "exact defect norm": float(np.linalg.norm(defect, ord=2)),
        "one-half-power coefficient": coefficient,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=288)
    parser.add_argument("--renewal-power", type=int, default=1)
    parser.add_argument("--maximum-mode", type=int, default=10)
    parser.add_argument("--spectral-size", type=int, default=32)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    source, reward = completed_reward_certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.renewal_power,
    )
    markov = markov_trace_certificate(
        reward,
        prime=3,
        maximum_mode=args.maximum_mode,
        seed=args.seed,
    )
    exact = exact_geometric_defect_certificate(3, args.spectral_size)

    print("identity=completed displacement trace domain and Markov operator")
    print("status=fixed-S trace owner exact; uniform bound open")
    for title, checks in (("source", source), ("markov", markov), ("exact", exact)):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            if isinstance(value, complex):
                print(f"{label.replace(' ', '_')}_real={value.real:.12e}")
                print(f"{label.replace(' ', '_')}_imag={value.imag:.12e}")
            else:
                print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_errors = (
        float(source["ambient reward commutator factorization error"]),
        float(source["Sonin commutator reconstruction error"]),
        float(source["outer commutator reconstruction error"]),
        float(source["direct-sum trace-norm scaling error"]),
        float(markov["relative Markov versus local Gram error"]),
        float(markov["relative probability normalization error"]),
        float(markov["maximum point Markov-defect error"]),
        float(markov["maximum completed second-difference error"]),
        float(markov["defect self-adjoint error"]),
        float(markov["defect minimum eigenvalue violation"]),
        float(exact["exact geometric average fixed-mode error"]),
        float(exact["exact defect positivity violation"]),
        float(exact["exact defect norm formula error"]),
    )
    maximum_exact_error = max(exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "completed Markov trace-domain certificate failed: "
            f"{maximum_exact_error:.6e}"
        )

    print("completed_reward_commutator_factorization=EXACT")
    print("fixed_s_displacement_coefficient=TRACE_CLASS_CONTINUOUS")
    print("relative_markov_operator=A_p_A_pSTAR")
    print("completed_mode_sum=ONE_OPERATOR_DEFECT")
    print("local_defect_norm=4a_p_over_1_plus_a_p_squared")
    print("trace_norm_used_for_uniform_gate=FALSE")
    print("complete_sonin_markov_defect_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
