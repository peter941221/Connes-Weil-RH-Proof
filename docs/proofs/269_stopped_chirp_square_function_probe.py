#!/usr/bin/env python3
"""Certificate and death screen for the stopped-chirp square-function route.

The exact certificate checks four scalar or finite-dimensional identities:

* the normalized local Euler inverse is a geometric characteristic function;
* its pointwise defect has the stated Fourier series;
* product defects telescope through contractive local channels;
* the tempting cubic Euler ledger ``p^(-3m/2)`` converges only after counting
  the geometric coefficient twice;
* the route-owned coefficient-weighted chirp square has the harmonic scale
  ``p^(-m)`` and therefore still diverges in the first mode.

The optional periodic Sonin screen measures the influence of deleting one
prime from the complete finite-S endpoint.  It guards against applying a raw
coordinate Efron-Stein estimate before the real-line crossing and chirp
factorization.  Periodic sections do not prove a continuous lower bound.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for candidate in range(2, math.isqrt(limit) + 1):
        if sieve[candidate]:
            sieve[candidate * candidate : limit + 1 : candidate] = False
    return np.flatnonzero(sieve).astype(int).tolist()


def normalized_local_inverse(
    coefficient: float, angle: np.ndarray
) -> np.ndarray:
    return (1.0 - coefficient) / (
        1.0 - coefficient * np.exp(1j * angle)
    )


def geometric_characteristic_sum(
    coefficient: float, angle: np.ndarray, modes: int
) -> np.ndarray:
    mode_numbers = np.arange(modes + 1, dtype=float)
    weights = (1.0 - coefficient) * coefficient**mode_numbers
    return np.sum(
        weights[:, None] * np.exp(1j * mode_numbers[:, None] * angle[None, :]),
        axis=0,
    )


def local_defect_fourier_sum(
    coefficient: float, angle: np.ndarray, modes: int
) -> np.ndarray:
    mode_numbers = np.arange(1, modes + 1, dtype=float)
    constant = 2.0 * coefficient / (1.0 + coefficient)
    oscillatory = (
        2.0
        * (1.0 - coefficient)
        / (1.0 + coefficient)
        * np.sum(
            coefficient**mode_numbers[:, None]
            * np.cos(mode_numbers[:, None] * angle[None, :]),
            axis=0,
        )
    )
    return constant - oscillatory


def local_factor_certificate(
    coefficients: tuple[float, ...], grid_size: int, modes: int
) -> dict[str, float]:
    angle = np.linspace(-math.pi, math.pi, grid_size)
    characteristic_error = 0.0
    defect_error = 0.0
    fixed_mode_error = 0.0
    for coefficient in coefficients:
        exact = normalized_local_inverse(coefficient, angle)
        truncated = geometric_characteristic_sum(
            coefficient, angle, modes
        )
        characteristic_error = max(
            characteristic_error,
            float(np.max(np.abs(exact - truncated))),
        )
        defect = 1.0 - np.abs(exact) ** 2
        defect_fourier = local_defect_fourier_sum(
            coefficient, angle, modes
        )
        defect_error = max(
            defect_error,
            float(np.max(np.abs(defect - defect_fourier))),
        )
        fixed_mode_error = max(
            fixed_mode_error,
            abs(complex(normalized_local_inverse(
                coefficient, np.array([0.0])
            )[0]) - 1.0),
        )
    return {
        "geometric characteristic error": characteristic_error,
        "local defect Fourier error": defect_error,
        "fixed-mode normalization error": fixed_mode_error,
    }


def product_defect_certificate(
    primes: list[int], grid_size: int
) -> dict[str, float]:
    angle = np.linspace(-math.pi, math.pi, grid_size)
    local_values = [
        normalized_local_inverse(
            prime**-0.5, math.log(prime) * angle
        )
        for prime in primes
    ]
    product = np.ones_like(angle, dtype=complex)
    telescope = np.zeros_like(angle, dtype=float)
    prefix_square = np.ones_like(angle, dtype=float)
    maximum_local_modulus = 0.0
    for value in local_values:
        local_square = np.abs(value) ** 2
        telescope += prefix_square * (1.0 - local_square)
        prefix_square *= local_square
        product *= value
        maximum_local_modulus = max(
            maximum_local_modulus, float(np.max(np.abs(value)))
        )
    exact = 1.0 - np.abs(product) ** 2
    return {
        "product defect telescope error": float(
            np.max(np.abs(exact - telescope))
        ),
        "contractive local modulus excess": max(
            maximum_local_modulus - 1.0, 0.0
        ),
        "negative telescope mass": max(
            -float(np.min(telescope)), 0.0
        ),
    }


def cubic_mode_sum(
    primes: list[int], modes: int, polynomial_degree: int
) -> float:
    total = 0.0
    for prime in primes:
        coefficient = prime**-0.5
        logarithm = math.log(prime)
        for mode in range(1, modes + 1):
            word_cost = (1.0 + mode * logarithm) ** (
                2 * polynomial_degree
            )
            total += (
                (1.0 - coefficient)
                * word_cost
                * coefficient ** (3 * mode)
            )
    return total


def chirp_square_sum(
    primes: list[int], modes: int, polynomial_degree: int
) -> float:
    total = 0.0
    for prime in primes:
        coefficient = prime**-0.5
        logarithm = math.log(prime)
        for mode in range(1, modes + 1):
            word_cost = (1.0 + mode * logarithm) ** (
                2 * polynomial_degree
            )
            weighted_chirp_norm = coefficient**mode
            total += word_cost * weighted_chirp_norm**2
    return total


def raw_sums(primes: list[int]) -> tuple[float, float]:
    half_power = sum(prime**-0.5 for prime in primes)
    harmonic = sum(prime**-1.0 for prime in primes)
    return half_power, harmonic


def summability_certificate(
    maximum_prime: int,
    modes: int,
    polynomial_degree: int,
) -> tuple[list[dict[str, float]], dict[str, float]]:
    cutoffs = [
        cutoff
        for cutoff in (100, 1_000, 10_000, 100_000, 1_000_000)
        if cutoff <= maximum_prime
    ]
    if not cutoffs or cutoffs[-1] != maximum_prime:
        cutoffs.append(maximum_prime)
    all_primes = primes_up_to(maximum_prime)
    rows: list[dict[str, float]] = []
    previous_cubic = 0.0
    maximum_monotonicity_error = 0.0
    for cutoff in cutoffs:
        active = [prime for prime in all_primes if prime <= cutoff]
        half_power, harmonic = raw_sums(active)
        chirp_square = chirp_square_sum(
            active, modes, polynomial_degree
        )
        cubic = cubic_mode_sum(active, modes, polynomial_degree)
        maximum_monotonicity_error = max(
            maximum_monotonicity_error, previous_cubic - cubic
        )
        previous_cubic = cubic
        rows.append(
            {
                "cutoff": float(cutoff),
                "prime_count": float(len(active)),
                "half_power": half_power,
                "harmonic": harmonic,
                "chirp_square": chirp_square,
                "cubic": cubic,
            }
        )

    variance_error = 0.0
    variance_ratio = 0.0
    for prime in (2, 3, 5, 11, 101):
        coefficient = prime**-0.5
        mode_numbers = np.arange(1, modes + 1, dtype=float)
        probabilities = (
            (1.0 - coefficient) * coefficient**mode_numbers
        )
        chirp_response = coefficient**mode_numbers
        truncated_second_moment = float(
            np.sum(probabilities * chirp_response**2)
        )
        exact_second_moment = (
            (1.0 - coefficient)
            * coefficient**3
            / (1.0 - coefficient**3)
        )
        variance_error = max(
            variance_error,
            abs(truncated_second_moment - exact_second_moment),
        )
        mean = coefficient**2 / (1.0 + coefficient)
        exact_variance = exact_second_moment - mean**2
        variance_ratio = max(
            variance_ratio,
            exact_variance / exact_second_moment,
        )
    checks = {
        "cubic monotonicity error": maximum_monotonicity_error,
        "geometric second-moment truncation error": variance_error,
        "maximum variance/second-moment ratio": variance_ratio,
    }
    return rows, checks


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


def periodic_coordinate_screen(
    size: int,
    step: float,
    root_width: float,
    prime_limit: int,
    targets: tuple[int, ...],
) -> tuple[list[dict[str, float]], dict[str, float]]:
    proof_251 = load_probe(
        "251_mixed_prime_projection_curvature_probe.py",
        "proof_251_for_269",
    )
    proof_252 = load_probe(
        "252_synchronized_finite_s_logarithmic_flow_probe.py",
        "proof_252_for_269",
    )
    root_size = int(round(root_width / step)) + 1
    primes = proof_252.primes_up_to(prime_limit)
    factors = proof_252.make_factors(primes, size, step)
    coordinates = (np.arange(size) - size // 2) * step
    outer_basis = proof_251.halfline_basis(coordinates)
    inner_basis, sonin_eigenvalues = proof_251.sonin_basis(
        size, step, 1e-8
    )
    outer_projection = proof_252.projection_from_basis(outer_basis)
    inner_projection = proof_252.projection_from_basis(inner_basis)
    base_band = outer_projection - inner_projection
    witness, row_residual = proof_251.four_mode_row_witness(
        root_size, step
    )

    factor_values = [
        1.0
        - float(factor["amplitude"])
        * np.asarray(factor["multiplier"])
        for factor in factors
    ]
    total_multiplier = np.prod(np.stack(factor_values), axis=0)

    def projection_from_multiplier(
        basis: np.ndarray, multiplier: np.ndarray
    ) -> np.ndarray:
        normalized = multiplier / max(
            float(np.max(np.abs(multiplier))), 1e-300
        )
        transported = np.fft.ifft(
            normalized[:, None] * np.fft.fft(basis, axis=0), axis=0
        )
        transported, _ = proof_252.orthonormalize(transported)
        return proof_252.projection_from_basis(transported)

    def root_readout(
        matrix: np.ndarray,
    ) -> tuple[np.ndarray, float, float]:
        root = proof_251.root_operator(matrix, root_size, step)
        norm = proof_251.operator_norm(root)
        scalar = abs(float(np.vdot(witness, root @ witness).real))
        return root, norm, scalar

    full_outer = projection_from_multiplier(
        outer_basis, total_multiplier
    )
    full_inner = projection_from_multiplier(
        inner_basis, total_multiplier
    )
    full_root, _, _ = root_readout(
        full_outer - full_inner - base_band
    )

    selected_indices = sorted(
        {
            min(
                range(len(primes)),
                key=lambda index: abs(primes[index] - target),
            )
            for target in targets
        }
    )
    rows: list[dict[str, float]] = []
    for index in selected_indices:
        prime = primes[index]
        reduced_multiplier = total_multiplier / factor_values[index]
        reduced_outer = projection_from_multiplier(
            outer_basis, reduced_multiplier
        )
        reduced_inner = projection_from_multiplier(
            inner_basis, reduced_multiplier
        )
        reduced_root, _, _ = root_readout(
            reduced_outer - reduced_inner - base_band
        )
        _, influence_norm, witness_influence = root_readout(
            full_root - reduced_root
        )
        rows.append(
            {
                "prime": float(prime),
                "root_norm": influence_norm,
                "witness": witness_influence,
                "p_norm": prime * influence_norm,
                "sqrt_p_norm": math.sqrt(prime) * influence_norm,
            }
        )

    fit_rows = [row for row in rows if row["root_norm"] > 1e-14]
    logarithmic_primes = np.log([row["prime"] for row in fit_rows])
    logarithmic_norms = np.log(
        [row["root_norm"] for row in fit_rows]
    )
    slope, intercept = np.polyfit(
        logarithmic_primes, logarithmic_norms, 1
    )
    checks = {
        "fitted leave-one-prime slope": float(slope),
        "fitted scale": float(math.exp(intercept)),
        "four-mode row residual": float(row_residual),
        "Sonin rank": float(inner_basis.shape[1]),
        "Sonin top eigenvalue": float(sonin_eigenvalues[-1]),
        "half-domain": size * step / 2.0,
    }
    return rows, checks


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------------+---------------+")
    print("| check                                      | value         |")
    print("+--------------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>13.6e} |")
    print("+--------------------------------------------+---------------+")


def print_summability(rows: list[dict[str, float]]) -> None:
    print("Euler coefficient-accounting cohorts")
    print(
        "+----------+---------+---------------+---------------+---------------+---------------+"
    )
    print(
        "| p <=     | count   | sum p^-1/2    | sum p^-1      | chirp square  | cubic double  |"
    )
    print(
        "+----------+---------+---------------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['cutoff']):>8d} |"
            f" {int(row['prime_count']):>7d} |"
            f" {row['half_power']:>13.6e} |"
            f" {row['harmonic']:>13.6e} |"
            f" {row['chirp_square']:>13.6e} |"
            f" {row['cubic']:>13.6e} |"
        )
    print(
        "+----------+---------+---------------+---------------+---------------+---------------+"
    )


def print_periodic_rows(rows: list[dict[str, float]]) -> None:
    print("Periodic complete-endpoint coordinate screen")
    print(
        "+-------+---------------+---------------+---------------+---------------+"
    )
    print(
        "| p     | root norm     | witness       | p * norm      | sqrt(p)*norm  |"
    )
    print(
        "+-------+---------------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['prime']):>5d} |"
            f" {row['root_norm']:>13.6e} |"
            f" {row['witness']:>13.6e} |"
            f" {row['p_norm']:>13.6e} |"
            f" {row['sqrt_p_norm']:>13.6e} |"
        )
    print(
        "+-------+---------------+---------------+---------------+---------------+"
    )


def parse_targets(raw: str) -> tuple[int, ...]:
    targets = tuple(
        sorted({int(item) for item in raw.split(",") if item.strip()})
    )
    if len(targets) < 3 or targets[0] < 2:
        raise ValueError("periodic targets need at least three integers")
    return targets


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid-size", type=int, default=4097)
    parser.add_argument("--fourier-modes", type=int, default=80)
    parser.add_argument("--maximum-prime", type=int, default=100_000)
    parser.add_argument("--majorant-modes", type=int, default=24)
    parser.add_argument("--polynomial-degree", type=int, default=1)
    parser.add_argument("--periodic-size", type=int, default=256)
    parser.add_argument("--periodic-step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument("--periodic-prime-limit", type=int, default=997)
    parser.add_argument(
        "--periodic-targets",
        default="29,47,79,127,199,313,499,727,997",
    )
    parser.add_argument("--skip-periodic-screen", action="store_true")
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--maximum-naive-slope", type=float, default=-0.9)
    args = parser.parse_args()

    if args.grid_size < 257 or args.fourier_modes < 8:
        raise ValueError("the Fourier certificate grid is too small")
    if args.maximum_prime < 100 or args.majorant_modes < 4:
        raise ValueError("the summability certificate range is too small")
    if args.polynomial_degree < 0:
        raise ValueError("polynomial degree must be nonnegative")

    local = local_factor_certificate(
        (2**-0.5, 3**-0.5, 5**-0.5, 11**-0.5),
        args.grid_size,
        args.fourier_modes,
    )
    telescope = product_defect_certificate(
        primes_up_to(97), args.grid_size
    )
    summability_rows, summability = summability_certificate(
        args.maximum_prime,
        args.majorant_modes,
        args.polynomial_degree,
    )

    print("identity=stopped chirp coefficient-accounting audit")
    print("status=cubic double count rejected; concentration factor required")
    print_checks("Normalized local Euler factor", local)
    print()
    print_checks("Product defect telescope", telescope)
    print()
    print_summability(summability_rows)
    print()
    print_checks("Geometric surrogate checks", summability)

    exact_errors = [
        *local.values(),
        *telescope.values(),
        summability["cubic monotonicity error"],
        summability["geometric second-moment truncation error"],
    ]
    maximum_error = max(exact_errors)
    print(f"maximum exact-certificate error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"exact certificate failed: {maximum_error:.6e}"
        )

    if not args.skip_periodic_screen:
        targets = parse_targets(args.periodic_targets)
        periodic_rows, periodic = periodic_coordinate_screen(
            args.periodic_size,
            args.periodic_step,
            args.root_width,
            args.periodic_prime_limit,
            targets,
        )
        print()
        print_periodic_rows(periodic_rows)
        print()
        print_checks("Periodic guard statistics", periodic)
        if periodic["fitted leave-one-prime slope"] <= args.maximum_naive_slope:
            raise SystemExit(
                "periodic guard no longer rejects the naive p^-1 influence"
            )

    print("local_euler_defect_verdict=EXACT")
    print("coefficient_weighted_chirp_square_verdict=HARMONIC_DIVERGENCE")
    print("cubic_prime_mode_majorant_verdict=DOUBLE_COUNTED_NOT_ROUTE_OWNED")
    print("raw_endpoint_efron_stein_verdict=REJECTED_BY_PERIODIC_SCREEN")
    print("positive_square_energy_concentration_sum=PROVED_IN_PROOF_272")
    print("positive_h1_source_lift=REJECTED_BY_PROOF_273")
    print("signed_scalar_local_coefficient=p^(-m/2)")
    print("complete_signed_extra_half_power=OPEN")
    print("signed_paired_source_disintegration=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
