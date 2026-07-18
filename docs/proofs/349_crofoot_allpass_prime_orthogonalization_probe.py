"""Certificate for Proof 349's Crofoot/all-pass orthogonalization.

The exact continuous statements are the kernel, model-space multiplier, and
inner-product telescoping identities in Proof 349.  The prime-cluster table
compares their diagonal arithmetic ledger with Proof 348's deliberately
premature localized Hilbert--Schmidt Gram.  It is not a finite-section proof of
Gate 3U.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for candidate in range(2, math.isqrt(limit) + 1):
        if not sieve[candidate]:
            continue
        start = candidate * candidate
        count = (limit - start) // candidate + 1
        sieve[start : limit + 1 : candidate] = b"\x00" * count
    return [value for value in range(2, limit + 1) if sieve[value]]


def theta(displacement: float, point: complex) -> complex:
    return np.exp(1j * displacement * point)


def frostman(inner_value: complex, coefficient: float) -> complex:
    return (inner_value - coefficient) / (1.0 - coefficient * inner_value)


def crofoot(inner_value: complex, coefficient: float) -> complex:
    return math.sqrt(1.0 - coefficient * coefficient) / (
        1.0 - coefficient * inner_value
    )


def exact_identity_checks() -> dict[str, float]:
    primes = [2, 3, 5, 7, 11]
    source = 0.37 + 0.19j
    target = -0.23 + 0.17j

    single_errors: list[float] = []
    beta_source: list[complex] = []
    beta_target: list[complex] = []
    theta_source: list[complex] = []
    theta_target: list[complex] = []

    for prime in primes:
        displacement = math.log(prime)
        coefficient = prime ** -0.5
        source_inner = theta(displacement, source)
        target_inner = theta(displacement, target)
        source_beta = frostman(source_inner, coefficient)
        target_beta = frostman(target_inner, coefficient)
        source_multiplier = crofoot(source_inner, coefficient)
        target_multiplier = crofoot(target_inner, coefficient)

        left = 1.0 - source_beta * np.conj(target_beta)
        right = (
            source_multiplier
            * np.conj(target_multiplier)
            * (1.0 - source_inner * np.conj(target_inner))
        )
        single_errors.append(abs(left - right) / max(1.0, abs(left)))
        beta_source.append(source_beta)
        beta_target.append(target_beta)
        theta_source.append(source_inner)
        theta_target.append(target_inner)

    prefix_source = 1.0 + 0.0j
    prefix_target = 1.0 + 0.0j
    telescoping = 0.0 + 0.0j
    for source_beta, target_beta in zip(beta_source, beta_target):
        telescoping += (
            prefix_source
            * np.conj(prefix_target)
            * (1.0 - source_beta * np.conj(target_beta))
        )
        prefix_source *= source_beta
        prefix_target *= target_beta
    telescoping_left = 1.0 - prefix_source * np.conj(prefix_target)

    q_source = 1.0 + 0.0j
    q_sharp_source = 1.0 + 0.0j
    for prime, source_inner in zip(primes, theta_source):
        coefficient = prime ** -0.5
        q_source *= 1.0 - coefficient * source_inner
        q_sharp_source *= source_inner - coefficient
    allpass_error = abs(q_sharp_source / q_source - prefix_source) / max(
        1.0, abs(prefix_source)
    )

    boundary_errors: list[float] = []
    for boundary_point in np.linspace(-2.0, 2.0, 41):
        product = 1.0 + 0.0j
        for prime in primes:
            inner_value = theta(math.log(prime), complex(boundary_point))
            product *= frostman(inner_value, prime ** -0.5)
        boundary_errors.append(abs(abs(product) - 1.0))

    return {
        "single Crofoot kernel error": max(single_errors),
        "all-pass quotient error": float(allpass_error),
        "cascade telescoping error": float(
            abs(telescoping_left - telescoping)
            / max(1.0, abs(telescoping_left))
        ),
        "boundary inner modulus error": max(boundary_errors),
    }


def disk_multiplier_check(seed: int) -> float:
    """Check q^(-1) K_(z^N) is orthogonal to beta H2 on a disk grid."""

    rng = np.random.default_rng(seed)
    delays = [2, 3, 5]
    coefficients = [2.0 ** -0.5, 3.0 ** -0.5, 5.0 ** -0.5]
    degree = sum(delays)
    grid_size = 1 << 16
    angles = 2.0 * math.pi * np.arange(grid_size) / grid_size
    points = np.exp(1j * angles)

    q = np.ones(grid_size, dtype=complex)
    q_sharp = np.ones(grid_size, dtype=complex)
    for delay, coefficient in zip(delays, coefficients):
        inner = points**delay
        q *= 1.0 - coefficient * inner
        q_sharp *= inner - coefficient
    beta = q_sharp / q

    polynomial_coefficients = rng.normal(size=degree) + 1j * rng.normal(
        size=degree
    )
    polynomial = np.polynomial.polynomial.polyval(points, polynomial_coefficients)
    transported = polynomial / q

    errors = []
    scale = max(1.0, float(np.sqrt(np.mean(np.abs(transported) ** 2))))
    for mode in range(32):
        target = beta * points**mode
        inner_product = np.mean(transported * np.conj(target))
        errors.append(abs(inner_product) / scale)
    return max(errors)


def cluster_statistics(
    lower: int,
    epsilon: float,
    root_half_width: float,
    all_primes: list[int],
    block_size: int = 512,
) -> tuple[int, float, float, float]:
    upper = (1.0 + epsilon) * lower
    cluster = np.asarray(
        [prime for prime in all_primes if lower <= prime <= upper], dtype=float
    )
    if cluster.size == 0:
        return 0, 0.0, 0.0, 0.0

    logs = np.log(cluster)
    weights = cluster ** -0.5
    cascade_ledger = float(
        np.sum(logs * (-np.log1p(-1.0 / cluster)))
    )

    gram = 0.0
    for start in range(0, cluster.size, block_size):
        stop = min(start + block_size, cluster.size)
        row_logs = logs[start:stop, None]
        differences = logs[None, :] - row_logs
        correlations = np.maximum(
            0.0, 1.0 - np.abs(differences) / (2.0 * root_half_width)
        )
        gram += float(
            np.sum(
                weights[start:stop, None]
                * weights[None, :]
                * np.minimum(row_logs, logs[None, :])
                * correlations
            )
        )

    whitened_mass = gram / (1.0 + gram)
    return int(cluster.size), cascade_ledger, gram, whitened_mass


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scales", default="100,1000,10000,100000,1000000")
    parser.add_argument("--epsilon", type=float, default=0.1)
    parser.add_argument("--root-half-width", type=float, default=0.5)
    parser.add_argument("--seed", type=int, default=349)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = exact_identity_checks()
    checks["disk multiplier orthogonality error"] = disk_multiplier_check(args.seed)

    print("Proof 349 Crofoot/all-pass prime orthogonalization certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"all-pass identity check failed: {maximum_error:.3e}")

    scales = [int(value) for value in args.scales.split(",")]
    prime_limit = math.ceil((1.0 + args.epsilon) * max(scales))
    all_primes = primes_up_to(prime_limit)

    print()
    print(
        "X          primes   cascade_ledger  raw_Gram_S2^2  "
        "Gram/ledger    whitened_mass"
    )
    for lower in scales:
        count, ledger, gram, whitened = cluster_statistics(
            lower,
            args.epsilon,
            args.root_half_width,
            all_primes,
        )
        ratio = gram / ledger if ledger else float("nan")
        print(
            f"{lower:9d}  "
            f"{count:7d}  "
            f"{ledger: .8e}  "
            f"{gram: .8e}  "
            f"{ratio: .8e}  "
            f"{whitened: .8e}"
        )

    print()
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("complete_allpass_model_range=EXACT")
    print("prime_cascade_orthogonality=EXACT")
    print("proof_343_burnol_quotient_bridge=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
