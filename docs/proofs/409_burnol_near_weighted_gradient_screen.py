"""Non-periodic Burnol near-region screen for the weighted Gate owner.

The source moment is the actual even cosine-transform Burnol window used by
Proof 334.  The Euler inverse metric is approximated by a binned convolution
of normalized signed geometric-difference laws.  This is a numerical screen,
not a proof of the continuous root-relative estimate.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np


def shifted_legendre_values(size: int, points: np.ndarray) -> np.ndarray:
    values = np.polynomial.legendre.legvander(2.0 * points - 1.0, size - 1)
    return values * np.sqrt(2.0 * np.arange(size, dtype=float) + 1.0)


@dataclass
class MomentEvaluator:
    size: int
    integration_order: int

    def __post_init__(self) -> None:
        self.quadrature_nodes, self.quadrature_weights = np.polynomial.legendre.leggauss(
            self.integration_order
        )
        self.points = 0.5 * (self.quadrature_nodes + 1.0)
        self.weights = 0.5 * self.quadrature_weights
        self.basis = shifted_legendre_values(self.size, self.points)
        self.weighted_basis = self.weights[:, None] * self.basis
        self.point_outer = np.outer(self.points, self.points)

    def interval_overlap(self, rho: float) -> np.ndarray:
        upper = min(1.0, 1.0 / rho)
        points = 0.5 * upper * (self.quadrature_nodes + 1.0)
        weights = 0.5 * upper * self.quadrature_weights
        output_values = shifted_legendre_values(self.size, points)
        input_values = shifted_legendre_values(self.size, rho * points)
        return math.sqrt(rho) * output_values.T @ (weights[:, None] * input_values)

    def cosine_rectangle(self, rho: float, orientation: int) -> np.ndarray:
        if orientation == 1:
            frequency = 2.0 * math.pi * rho
            amplitude = 2.0 * math.sqrt(rho)
        elif orientation == -1:
            frequency = 2.0 * math.pi / rho
            amplitude = 2.0 / math.sqrt(rho)
        else:
            raise ValueError("orientation must be +1 or -1")
        kernel = amplitude * np.cos(frequency * self.point_outer)
        return self.weighted_basis.T @ kernel @ self.weighted_basis

    def moment(self, displacement: float) -> np.ndarray:
        rho = math.exp(displacement)
        direct = self.interval_overlap(rho)
        reverse = self.interval_overlap(1.0 / rho)
        forward_fourier = self.cosine_rectangle(rho, 1)
        reverse_fourier = self.cosine_rectangle(rho, -1)
        return np.block(
            [[direct, forward_fourier], [reverse_fourier, reverse]]
        ).astype(complex)


def compact_phi_and_qphi(points: np.ndarray, radius: float) -> tuple[np.ndarray, np.ndarray]:
    scaled = points / radius
    inside = np.abs(scaled) < 1.0
    phi = np.zeros_like(points)
    second = np.zeros_like(points)
    x = scaled[inside]
    phi[inside] = (1.0 - x * x) ** 4
    second[inside] = (
        -8.0 + 72.0 * x * x - 120.0 * x**4 + 56.0 * x**6
    ) / (radius * radius)
    return phi, -second + 0.25 * phi


def geometric_factor(
    prime: int, grid_step: float, maximum_power: int
) -> tuple[np.ndarray, int, float]:
    a = prime ** -0.5
    rho = (1.0 - a) / (1.0 + a)
    ell = math.log(prime)
    radius = int(math.ceil(maximum_power * ell / grid_step))
    values = np.zeros(2 * radius + 1, dtype=float)
    for power in range(-maximum_power, maximum_power + 1):
        index = radius + int(round(power * ell / grid_step))
        values[index] += rho * a ** abs(power)
    omitted_mass = 2.0 * rho * a ** (maximum_power + 1) / (1.0 - a)
    return values, radius, omitted_mass


def euler_difference_law(
    primes: list[int], grid_step: float, maximum_power: int
) -> tuple[np.ndarray, int, float]:
    law = np.array([1.0])
    origin = 0
    omitted_mass = 0.0
    for prime in primes:
        factor, factor_origin, factor_tail = geometric_factor(
            prime, grid_step, maximum_power
        )
        law = np.convolve(law, factor)
        origin += factor_origin
        omitted_mass += factor_tail
    total_mass = float(law.sum())
    if total_mass > 1.0:
        raise RuntimeError("truncated geometric law has mass above one")
    return law, origin, min(1.0, omitted_mass)


def screen_one(
    primes: list[int],
    size: int,
    radius: float,
    quadrature_order: int,
    integration_order: int,
    grid_step: float,
    maximum_power: int,
) -> dict[str, float]:
    evaluator = MomentEvaluator(size, integration_order)
    root_nodes, root_weights = np.polynomial.legendre.leggauss(quadrature_order)
    root_nodes = radius * root_nodes
    root_weights = radius * root_weights
    phi, qphi = compact_phi_and_qphi(root_nodes, radius)
    root_budget = math.sqrt(
        float(np.sum(root_weights * (phi * phi + qphi * qphi)))
    )

    near_cutoff = 4.0 * radius + 4.0
    law, origin, omitted_mass = euler_difference_law(
        primes, grid_step, maximum_power
    )
    displacements = (np.arange(law.size) - origin) * grid_step
    mask = np.abs(displacements) <= near_cutoff
    near_mass = float(law[mask].sum())

    moment_cache: dict[float, np.ndarray] = {}

    def get_moment(displacement: float) -> np.ndarray:
        key = round(float(displacement), 12)
        if key not in moment_cache:
            moment_cache[key] = evaluator.moment(key)
        return moment_cache[key]

    zero_moment = get_moment(0.0)
    source_detector = np.zeros_like(zero_moment)
    for shift, weight in zip(root_nodes, root_weights * qphi):
        source_detector += weight * get_moment(float(shift))

    gram_inverse = np.linalg.inv(zero_moment)
    gram_condition = float(np.linalg.cond(zero_moment))
    full_gram = np.zeros_like(zero_moment)
    near_numerator = np.zeros_like(zero_moment)
    for displacement, probability in zip(displacements, law):
        moment = get_moment(float(displacement))
        full_gram += probability * moment
        if not abs(displacement) <= near_cutoff:
            continue
        shifted_detector = np.zeros_like(zero_moment)
        for shift, weight in zip(root_nodes, root_weights * qphi):
            shifted_detector += weight * get_moment(float(displacement + shift))
        near_numerator += probability * shifted_detector

    source_response = np.trace(gram_inverse @ source_detector)
    full_gram_condition = float(np.linalg.cond(full_gram))
    transported_near_response = np.trace(np.linalg.solve(full_gram, near_numerator))
    relative_near_response = transported_near_response - source_response
    return {
        "near_mass": near_mass,
        "omitted_geometric_mass_bound": omitted_mass,
        "gram_condition": gram_condition,
        "full_gram_condition": full_gram_condition,
        "source_response": float(source_response.real),
        "transported_near_response": float(transported_near_response.real),
        "near_response": float(relative_near_response.real),
        "near_response_abs": float(abs(relative_near_response)),
        "near_response_over_root_budget_sq": float(
            abs(relative_near_response) / max(root_budget * root_budget, 1e-15)
        ),
        "root_budget": root_budget,
        "moment_evaluations": float(len(moment_cache)),
    }


def parse_prime_sets(value: str) -> list[list[int]]:
    output = []
    for item in value.split(";"):
        output.append([int(prime) for prime in item.split(",") if prime])
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-sets", default="2;2,3;2,3,5;2,3,5,7;2,3,5,7,11;101,103,107")
    parser.add_argument("--sizes", default="8,12")
    parser.add_argument("--radius", type=float, default=1.2)
    parser.add_argument("--quadrature-order", type=int, default=20)
    parser.add_argument("--integration-order", type=int, default=64)
    parser.add_argument("--grid-step", type=float, default=0.12)
    parser.add_argument("--maximum-power", type=int, default=18)
    args = parser.parse_args()

    prime_sets = parse_prime_sets(args.prime_sets)
    sizes = [int(size) for size in args.sizes.split(",")]
    print("Proof 409 non-periodic Burnol near weighted-gradient screen")
    print("owner=Proof341_inverse_after_average_Burnol_boundary_Gram")
    print("finite_screen_is_proof=FALSE")
    print("table=BEGIN")
    for size in sizes:
        for primes in prime_sets:
            row = screen_one(
                primes,
                size,
                args.radius,
                args.quadrature_order,
                args.integration_order,
                args.grid_step,
                args.maximum_power,
            )
            print(
                f"size={size:2d} primes={','.join(map(str, primes)):>18s} "
                f"near_mass={row['near_mass']:.6e} "
                f"tail_bound={row['omitted_geometric_mass_bound']:.3e} "
                f"gram_cond={row['gram_condition']:.3e} "
                f"full_cond={row['full_gram_condition']:.3e} "
                f"near_response={row['near_response']:+.6e} "
                f"abs_response={row['near_response_abs']:.6e} "
                f"normalized={row['near_response_over_root_budget_sq']:.6e}"
            )
    print("table=END")
    print("burnol_nonperiodic_carrier=SCREENED")
    print("complete_metric_positivity=NOT_CERTIFIED")
    print("far_cosine_quadrature=UNRESOLVED")
    print("near_weighted_gradient=DIAGNOSTIC_ONLY")
    print("continuous_root_relative_gradient=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
