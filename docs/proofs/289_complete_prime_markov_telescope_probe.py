#!/usr/bin/env python3
"""Certificate for Proof 289's complete-prime Markov telescope."""

from __future__ import annotations

import argparse
import math

import numpy as np


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def parse_primes(raw_primes: str) -> list[int]:
    primes = [int(value.strip()) for value in raw_primes.split(",")]
    if not primes or len(set(primes)) != len(primes):
        raise ValueError("primes must be a nonempty list without duplicates")
    if any(not is_prime(prime) for prime in primes):
        raise ValueError("every entry in --primes must be prime")
    return sorted(primes)


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 1
    return True


def translation(frequencies: np.ndarray, displacement: float) -> np.ndarray:
    return np.diag(np.exp(1j * frequencies * displacement))


def local_factor(
    frequencies: np.ndarray, prime: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    size = frequencies.size
    identity = np.eye(size, dtype=complex)
    coefficient = prime**-0.5
    unitary = translation(frequencies, math.log(prime))
    resolvent = np.linalg.inv(identity - coefficient * unitary)
    average = (1.0 - coefficient) * resolvent
    markov = average @ average.conj().T
    defect_factorization = (
        coefficient
        * resolvent
        @ (identity - unitary)
        @ (identity - unitary.conj().T)
        @ resolvent.conj().T
    )
    return average, markov, identity - markov, defect_factorization


def exact_norm_certificate(primes: list[int]) -> dict[str, float]:
    maximum_error = 0.0
    maximum_positivity_violation = 0.0
    for prime in primes:
        coefficient = prime**-0.5
        angles = np.array([0.0, math.pi / 3.0, math.pi, 1.7 * math.pi])
        unitary = np.diag(np.exp(1j * angles))
        identity = np.eye(angles.size, dtype=complex)
        average = (1.0 - coefficient) * np.linalg.inv(
            identity - coefficient * unitary
        )
        defect = identity - average @ average.conj().T
        expected_norm = 4.0 * coefficient / (1.0 + coefficient) ** 2
        maximum_error = max(
            maximum_error,
            abs(float(np.linalg.norm(defect, ord=2)) - expected_norm),
        )
        maximum_positivity_violation = max(
            maximum_positivity_violation,
            -float(np.min(np.linalg.eigvalsh(defect))),
        )
    return {
        "maximum exact local defect norm error": maximum_error,
        "maximum local defect positivity violation": max(
            maximum_positivity_violation, 0.0
        ),
    }


def telescope_certificate(
    primes: list[int], spectral_size: int, seed: int
) -> tuple[dict[str, float], list[np.ndarray], np.ndarray]:
    if spectral_size < 8:
        raise ValueError("spectral size must be at least eight")
    generator = np.random.default_rng(seed)
    frequencies = np.sort(generator.uniform(-4.0, 4.0, spectral_size))
    frequencies[spectral_size // 2] = 0.0
    identity = np.eye(spectral_size, dtype=complex)
    reward = (
        generator.standard_normal((spectral_size, spectral_size))
        + 1j * generator.standard_normal((spectral_size, spectral_size))
    ) / spectral_size**1.5

    averages: list[np.ndarray] = []
    markov_operators: list[np.ndarray] = []
    local_terms: list[np.ndarray] = []
    prefix_markov = identity.copy()
    prefix_average = identity.copy()
    maximum_factorization_error = 0.0
    maximum_covariance_error = 0.0
    maximum_local_positivity_violation = 0.0

    for prime in primes:
        average, markov, defect, factorization = local_factor(
            frequencies, prime
        )
        averages.append(average)
        markov_operators.append(markov)
        maximum_factorization_error = max(
            maximum_factorization_error,
            relative_error(defect, factorization),
        )
        maximum_local_positivity_violation = max(
            maximum_local_positivity_violation,
            -float(np.min(np.linalg.eigvalsh(defect))),
        )

        local_term = prefix_markov @ defect
        local_terms.append(local_term)
        future_reward = prefix_average @ reward @ prefix_average.conj().T
        centered_covariance_trace = np.trace(future_reward) - np.trace(
            average @ future_reward @ average.conj().T
        )
        markov_trace = np.trace(local_term @ reward)
        maximum_covariance_error = max(
            maximum_covariance_error,
            abs(centered_covariance_trace - markov_trace),
        )
        prefix_markov = prefix_markov @ markov
        prefix_average = prefix_average @ average

    local_sum = sum(local_terms, np.zeros_like(identity))
    global_defect = identity - prefix_markov
    operator_telescope_error = relative_error(local_sum, global_defect)
    scalar_telescope_error = abs(
        sum(np.trace(term @ reward) for term in local_terms)
        - np.trace(global_defect @ reward)
    )

    displacement = 0.731
    displacement_operator = translation(frequencies, displacement)
    displaced_telescope_error = abs(
        sum(
            np.trace(displacement_operator @ term @ reward)
            for term in local_terms
        )
        - np.trace(displacement_operator @ global_defect @ reward)
    )
    global_positivity_violation = max(
        -float(np.min(np.linalg.eigvalsh(global_defect))), 0.0
    )
    global_contraction_violation = max(
        float(np.linalg.norm(global_defect, ord=2)) - 1.0, 0.0
    )

    return {
        "maximum local resolvent factorization error": (
            maximum_factorization_error
        ),
        "maximum centered covariance readback error": (
            maximum_covariance_error
        ),
        "operator prime telescope error": operator_telescope_error,
        "scalar prime telescope error": scalar_telescope_error,
        "displaced scalar telescope error": displaced_telescope_error,
        "maximum spectral local positivity violation": max(
            maximum_local_positivity_violation, 0.0
        ),
        "global defect positivity violation": global_positivity_violation,
        "global defect contraction violation": global_contraction_violation,
        "global defect operator norm": float(
            np.linalg.norm(global_defect, ord=2)
        ),
    }, local_terms, global_defect


def ownership_guards(
    local_terms: list[np.ndarray], global_defect: np.ndarray
) -> dict[str, float]:
    rows = np.stack([np.real(np.diag(term)) for term in local_terms])
    total = np.real(np.diag(global_defect))
    total_norm = float(np.linalg.norm(total))
    if total_norm <= 1e-14:
        raise RuntimeError("degenerate global defect in ownership guard")

    residual = rows[0] - np.dot(rows[0], total) / total_norm**2 * total
    if np.linalg.norm(residual) <= 1e-12 and len(rows) > 1:
        residual = rows[1] - np.dot(rows[1], total) / total_norm**2 * total
    residual /= max(float(np.linalg.norm(residual)), 1e-15)
    reward_diagonal = residual + 0.01 * total / total_norm
    prime_scalars = rows @ reward_diagonal
    completed_scalar = float(np.dot(total, reward_diagonal))
    triangle_ratio = float(
        np.sum(np.abs(prime_scalars)) / max(abs(completed_scalar), 1e-15)
    )

    varying_scalars = np.array(
        [
            (1.0 + 0.05 * index)
            * float(np.dot(row, reward_diagonal))
            for index, row in enumerate(rows)
        ]
    )
    varying_reward_gap = abs(
        float(np.sum(varying_scalars)) - completed_scalar
    )
    return {
        "primewise absolute-value cancellation ratio": triangle_ratio,
        "non-common reward telescope gap": varying_reward_gap,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--primes", default="2,3,5,7,11,13,17,19,23"
    )
    parser.add_argument("--spectral-size", type=int, default=56)
    parser.add_argument("--seed", type=int, default=289)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--guard-floor", type=float, default=2.0)
    args = parser.parse_args()

    primes = parse_primes(args.primes)
    telescope, local_terms, global_defect = telescope_certificate(
        primes, args.spectral_size, args.seed
    )
    exact_norm = exact_norm_certificate(primes)
    guards = ownership_guards(local_terms, global_defect)

    print("identity=complete-prime relative Markov telescope")
    print("status=prime summation exact; global renewal boundary bound open")
    for title, checks in (
        ("telescope", telescope),
        ("exact_norm", exact_norm),
        ("ownership_guard", guards),
    ):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_errors = (
        *(
            float(telescope[label])
            for label in (
                "maximum local resolvent factorization error",
                "maximum centered covariance readback error",
                "operator prime telescope error",
                "scalar prime telescope error",
                "displaced scalar telescope error",
                "maximum spectral local positivity violation",
                "global defect positivity violation",
                "global defect contraction violation",
            )
        ),
        float(exact_norm["maximum exact local defect norm error"]),
        float(exact_norm["maximum local defect positivity violation"]),
    )
    maximum_exact_error = max(exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "complete-prime Markov telescope certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if (
        float(guards["primewise absolute-value cancellation ratio"])
        < args.guard_floor
    ):
        raise SystemExit("primewise absolute-value guard was not separated")
    if float(guards["non-common reward telescope gap"]) <= args.tolerance:
        raise SystemExit("non-common reward ownership guard was not separated")

    print("complete_prime_markov_telescope=EXACT")
    print("predictable_future_factors=RETAINED")
    print("common_completed_reward=MANDATORY")
    print("primewise_extra_half_power_required=FALSE_FOR_SIGNED_SUM")
    print("trace_norm_used_for_uniform_gate=FALSE")
    print("global_renewal_boundary_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
