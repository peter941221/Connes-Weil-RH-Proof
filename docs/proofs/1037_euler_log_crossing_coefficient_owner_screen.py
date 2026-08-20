#!/usr/bin/env python3
"""Screen the exact Euler-log crossing coefficient owner.

The formal owner in ``SelectedCrossingKernel`` has two independent pieces:

* the logarithmic derivative of ``T_p(t) = I - t p^(-1/2) U_log(p)``, whose
  integrated coefficient is ``p^(-m/2) / m``;
* the two half-line crossing orientations, whose diagonal sum is
  ``m log(p) * (F(m log(p)) + F(-m log(p)))`` for one convolution square
  ``F = g^* * g``.

This finite numerical screen keeps one sampled root owner for all moments,
the convolution square, and the crossing readback.  It checks the local
Euler expansion, the direct crossing integral, prime powers through m=3, and
the absence of mixed-prime terms in a product of commuting Euler factors.
It is evidence for normalization and ownership only, not a Lean proof or an
RH result.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss


VANISHING_NODES = (0.0, 0.5, 1.0)


def integrate(values: np.ndarray, _nodes: np.ndarray, weights: np.ndarray) -> complex:
    """Integrate values already sampled at Gauss-Legendre nodes."""
    return complex(np.sum(weights * values))


def gauss_interval(left: float, right: float, order: int) -> tuple[np.ndarray, np.ndarray]:
    if not left < right:
        raise ValueError("expected a nonempty integration interval")
    reference_nodes, reference_weights = leggauss(order)
    nodes = (left + right) / 2.0 + (right - left) / 2.0 * reference_nodes
    weights = (right - left) / 2.0 * reference_weights
    return nodes, weights


def smooth_bump(x: np.ndarray, center: float, radius: float) -> np.ndarray:
    """A C-infinity bump supported in (center-radius, center+radius)."""
    z = (x - center) / radius
    result = np.zeros_like(x, dtype=float)
    mask = np.abs(z) < 1.0
    result[mask] = np.exp(-1.0 / (1.0 - z[mask] ** 2))
    return result


@dataclass(frozen=True)
class RootOwner:
    """One root reused by moments, F=g^* * g, and all readback terms."""

    label: str
    coefficients: np.ndarray
    centers: np.ndarray
    width: float
    support_bound: float
    grid: np.ndarray
    values: np.ndarray
    step: float
    moment_residual: float
    mass: float

    def evaluate(self, x: np.ndarray | float) -> np.ndarray:
        points = np.asarray(x, dtype=float)
        result = np.zeros_like(points, dtype=float)
        for coefficient, center in zip(self.coefficients, self.centers, strict=True):
            result += coefficient * smooth_bump(points, center, self.width)
        return result

    def laplace(self, s: float, order: int = 320) -> float:
        nodes, weights = gauss_interval(-self.support_bound, self.support_bound, order)
        return float(np.sum(weights * np.exp(s * nodes) * self.evaluate(nodes)))

    def convolution_square_direct(self, amount: float, order: int = 360) -> complex:
        """Directly evaluate F(amount)=int conj(g(u))*g(u+amount) du."""
        left = -self.support_bound - max(amount, 0.0)
        right = self.support_bound - min(amount, 0.0)
        nodes, weights = gauss_interval(left, right, order)
        values = np.conj(self.evaluate(nodes)) * self.evaluate(nodes + amount)
        return integrate(values, nodes, weights)

    def crossing_orientation(self, amount: float, reverse: bool, order: int = 280) -> complex:
        """Direct two-stage quadrature for one half-line crossing orientation."""
        if amount < 0.0:
            raise ValueError("crossing length must be nonnegative")
        source_nodes, source_weights = gauss_interval(0.0, amount, order)
        # The source variable only changes the translated kernel coordinate;
        # the inner integral is evaluated separately to retain the crossing
        # geometry instead of inserting the length factor by hand.
        inner_left = -self.support_bound - amount
        inner_right = self.support_bound
        inner_nodes, inner_weights = gauss_interval(inner_left, inner_right, order)
        if reverse:
            inner_values = np.conj(self.evaluate(inner_nodes + amount)) * self.evaluate(inner_nodes)
        else:
            inner_values = np.conj(self.evaluate(inner_nodes)) * self.evaluate(inner_nodes + amount)
        inner_value = integrate(inner_values, inner_nodes, inner_weights)
        return integrate(
            np.full(source_nodes.shape, inner_value, dtype=complex),
            source_nodes,
            source_weights,
        )

    def crossing_pair(self, amount: float, order: int = 280) -> complex:
        return self.crossing_orientation(amount, False, order) + self.crossing_orientation(
            amount, True, order
        )


def make_root_owner(
    *,
    label: str,
    support_radius: float,
    grid_size: int,
    step: float,
    basis_size: int,
    seed: int,
    signal_primes: tuple[int, ...],
) -> RootOwner:
    if grid_size % 2 or grid_size < 128:
        raise ValueError("grid_size must be an even integer at least 128")
    if support_radius <= 0.0 or step <= 0.0:
        raise ValueError("support_radius and step must be positive")
    centers = np.linspace(-0.60 * support_radius, 0.60 * support_radius, basis_size)
    width = 0.35 * support_radius
    support_bound = 0.95 * support_radius
    grid = (np.arange(grid_size) - grid_size // 2) * step
    basis = np.stack([smooth_bump(grid, center, width) for center in centers], axis=1)

    moment_nodes, moment_weights = gauss_interval(-support_bound, support_bound, 420)
    moment_basis = np.stack(
        [smooth_bump(moment_nodes, center, width) for center in centers], axis=1
    )
    moment_rows = np.stack(
        [
            np.sum(moment_weights[:, None] * np.exp(s * moment_nodes)[:, None] * moment_basis, axis=0)
            for s in VANISHING_NODES
        ]
    )
    _left, singular_values, right_vectors = np.linalg.svd(moment_rows, full_matrices=True)
    rank = int(np.sum(singular_values > 1.0e-11 * max(singular_values[0], 1.0)))
    nullspace = right_vectors[rank:].T
    if nullspace.shape[1] == 0:
        raise RuntimeError("triple-vanishing nullspace is empty")

    rng = np.random.default_rng(seed)
    candidates: list[tuple[np.ndarray, np.ndarray, float]] = []
    for _ in range(160):
        raw_coefficients = nullspace @ rng.normal(size=nullspace.shape[1])
        raw_values = basis @ raw_coefficients
        mass = float(np.sum(step * raw_values * raw_values))
        if mass <= 1.0e-18:
            continue
        coefficients = raw_coefficients / math.sqrt(mass)
        values = raw_values / math.sqrt(mass)
        signal = 0.0
        candidate = RootOwner(
            label,
            coefficients,
            centers,
            width,
            support_bound,
            grid,
            values,
            step,
            0.0,
            float(np.sum(step * values * values)),
        )
        for prime in signal_primes:
            for power in (1, 2, 3):
                amount = power * math.log(prime)
                signal += abs(candidate.convolution_square_direct(amount, order=180))
        candidates.append((coefficients, values, signal))
    if not candidates:
        raise RuntimeError("failed to construct a nonzero root")

    coefficients, values, _signal = max(candidates, key=lambda row: row[2])
    owner = RootOwner(
        label,
        coefficients,
        centers,
        width,
        support_bound,
        grid,
        values,
        step,
        0.0,
        float(np.sum(step * values * values)),
    )
    residual = max(abs(owner.laplace(s, order=520)) for s in VANISHING_NODES)
    return RootOwner(
        owner.label,
        owner.coefficients,
        owner.centers,
        owner.width,
        owner.support_bound,
        owner.grid,
        owner.values,
        owner.step,
        residual,
        owner.mass,
    )


def local_log_derivative_eigenvalue(
    t: np.ndarray, a: float, phase: complex
) -> np.ndarray:
    return -a * phase / (1.0 - t * a * phase)


def euler_flow_screen(
    primes: tuple[int, ...],
    frequencies: np.ndarray,
    quadrature_order: int,
    series_order: int,
) -> dict[str, float]:
    t_nodes, t_weights = gauss_interval(0.0, 1.0, quadrature_order)
    local_errors: list[float] = []
    for prime in primes:
        a = prime ** -0.5
        phases = np.exp(-1j * frequencies * math.log(prime))
        integrated = np.sum(
            t_weights[:, None]
            * local_log_derivative_eigenvalue(t_nodes[:, None], a, phases[None, :]),
            axis=0,
        )
        series = np.zeros_like(phases)
        for power in range(1, series_order + 1):
            series -= (a**power / power) * phases**power
        local_errors.append(float(np.max(np.abs(integrated - series))))

    # For commuting local factors, d/dt log(prod T_p) is the sum of the
    # local logarithmic derivatives.  The direct product quotient below
    # retains all apparent mixed words, so the residual tests their exact
    # cancellation rather than assuming it symbolically.
    factors = []
    local_terms = []
    for prime in primes:
        a = prime ** -0.5
        phase = np.exp(-1j * frequencies * math.log(prime))
        factors.append((a, phase))
        local_terms.append(local_log_derivative_eigenvalue(t_nodes[:, None], a, phase[None, :]))
    product = np.ones((t_nodes.size, frequencies.size), dtype=complex)
    for a, phase in factors:
        product *= 1.0 - t_nodes[:, None] * a * phase[None, :]
    derivative_product = np.zeros_like(product)
    for index, (a, phase) in enumerate(factors):
        derivative_factor = -a * phase[None, :]
        other = np.ones_like(product)
        for other_index, (other_a, other_phase) in enumerate(factors):
            if other_index != index:
                other *= 1.0 - t_nodes[:, None] * other_a * other_phase[None, :]
        derivative_product += derivative_factor * other
    direct_product_log_derivative = derivative_product / product
    summed_local_log_derivative = np.sum(np.stack(local_terms, axis=0), axis=0)
    mixed_residual = float(np.max(np.abs(direct_product_log_derivative - summed_local_log_derivative)))
    integrated_product = np.sum(t_weights[:, None] * direct_product_log_derivative, axis=0)
    integrated_sum = np.sum(t_weights[:, None] * summed_local_log_derivative, axis=0)
    integrated_additivity_residual = float(np.max(np.abs(integrated_product - integrated_sum)))
    return {
        "local_series_error": max(local_errors),
        "mixed_log_derivative_error": mixed_residual,
        "mixed_integrated_additivity_error": integrated_additivity_residual,
    }


def finite_prime_term(owner: RootOwner, prime: int, power: int, order: int) -> complex:
    amount = power * math.log(prime)
    symmetric_value = owner.convolution_square_direct(amount, order) + owner.convolution_square_direct(
        -amount, order
    )
    return math.log(prime) * prime ** (-0.5 * power) * symmetric_value


def crossing_coefficient_rows(
    owner: RootOwner,
    primes: tuple[int, ...],
    max_power: int,
    order: int,
) -> tuple[list[dict[str, float]], float, float]:
    rows: list[dict[str, float]] = []
    crossing_identity_errors: list[float] = []
    coefficient_errors: list[float] = []
    for prime in primes:
        for power in range(1, max_power + 1):
            amount = power * math.log(prime)
            direct_pair = owner.crossing_pair(amount, order)
            direct_square = owner.convolution_square_direct(amount, order) + owner.convolution_square_direct(
                -amount, order
            )
            expected_pair = amount * direct_square
            crossing_error = abs(direct_pair - expected_pair) / max(abs(expected_pair), 1.0e-14)
            weighted_pair = prime ** (-0.5 * power) / power * direct_pair
            expected_term = finite_prime_term(owner, prime, power, order)
            coefficient_error = abs(weighted_pair - expected_term) / max(abs(expected_term), 1.0e-14)
            rows.append(
                {
                    "prime": float(prime),
                    "power": float(power),
                    "amount": amount,
                    "symmetric_square": float(direct_square.real),
                    "crossing_pair": float(direct_pair.real),
                    "crossing_identity_error": crossing_error,
                    "weighted_pair": float(weighted_pair.real),
                    "finite_prime_term": float(expected_term.real),
                    "coefficient_error": coefficient_error,
                }
            )
            crossing_identity_errors.append(crossing_error)
            coefficient_errors.append(coefficient_error)
    return rows, max(crossing_identity_errors), max(coefficient_errors)


def mixed_prime_readback(
    owner: RootOwner, primes: tuple[int, ...], order: int
) -> float:
    """Check additivity of the crossing readback over a finite prime set."""
    terms = [(prime, power) for prime in primes for power in (1, 2)]
    summed = sum((finite_prime_term(owner, prime, power, order) for prime, power in terms), 0j)
    pair_sum = 0j
    for prime, power in terms:
        amount = power * math.log(prime)
        pair_sum += prime ** (-0.5 * power) / power * owner.crossing_pair(amount, order)
    return float(abs(summed - pair_sum) / max(abs(summed), 1.0e-14))


def parse_primes(raw: str) -> tuple[int, ...]:
    values = tuple(int(piece.strip()) for piece in raw.split(",") if piece.strip())
    if not values or any(value < 2 for value in values):
        raise ValueError("primes must be positive integers at least 2")
    if len(set(values)) != len(values):
        raise ValueError("primes must be distinct")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid-size", type=int, default=256)
    parser.add_argument("--step", type=float, default=0.06)
    parser.add_argument("--basis-size", type=int, default=12)
    parser.add_argument("--support-radius", type=float, default=1.80)
    parser.add_argument("--seed", type=int, default=1037)
    parser.add_argument("--primes", default="2,3")
    parser.add_argument("--flow-grid-size", type=int, default=96)
    parser.add_argument("--flow-quadrature", type=int, default=160)
    parser.add_argument("--series-order", type=int, default=64)
    parser.add_argument("--quadrature", type=int, default=260)
    parser.add_argument("--max-power", type=int, default=3)
    parser.add_argument("--tolerance", type=float, default=2.0e-8)
    args = parser.parse_args()
    primes = parse_primes(args.primes)
    if args.max_power < 3:
        raise ValueError("max_power must include m=1,2,3")
    if args.flow_grid_size < 16 or args.flow_grid_size % 2:
        raise ValueError("flow_grid_size must be an even integer at least 16")

    owner = make_root_owner(
        label="1037_same_owner_triple_vanishing_root",
        support_radius=args.support_radius,
        grid_size=args.grid_size,
        step=args.step,
        basis_size=args.basis_size,
        seed=args.seed,
        signal_primes=primes,
    )
    flow_step = 2.0 * math.pi / args.flow_grid_size
    frequencies = 2.0 * math.pi * np.fft.fftfreq(args.flow_grid_size, d=flow_step)
    flow = euler_flow_screen(
        primes, frequencies, args.flow_quadrature, args.series_order
    )
    rows, crossing_error, coefficient_error = crossing_coefficient_rows(
        owner, primes, args.max_power, args.quadrature
    )
    mixed_readback_error = mixed_prime_readback(owner, primes, args.quadrature)

    print("1037 Euler-log crossing coefficient-owner screen")
    print("formal_owner=SelectedCrossingKernel.eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow")
    print("owner_contract=g -> g^* * g -> both crossing orientations -> finitePrimeTerm")
    print(f"primes={primes} max_power={args.max_power}")
    print(f"owner_mass={owner.mass:.12e}")
    print(f"owner_support_bound={owner.support_bound:.12e}")
    print(f"owner_triple_vanishing_residual={owner.moment_residual:.12e}")
    print()
    print("flow_table=BEGIN")
    print(
        f"local_series_error={flow['local_series_error']:.12e} "
        f"mixed_log_derivative_error={flow['mixed_log_derivative_error']:.12e} "
        f"mixed_integrated_additivity_error={flow['mixed_integrated_additivity_error']:.12e}"
    )
    print("flow_table=END")
    print()
    print("prime_power_table=BEGIN")
    for row in rows:
        print(
            f"p={int(row['prime'])} m={int(row['power'])} "
            f"b={row['amount']:.12e} "
            f"Fsym={row['symmetric_square']:.12e} "
            f"crossing={row['crossing_pair']:.12e} "
            f"crossing_error={row['crossing_identity_error']:.12e} "
            f"weighted={row['weighted_pair']:.12e} "
            f"finite_term={row['finite_prime_term']:.12e} "
            f"coefficient_error={row['coefficient_error']:.12e}"
        )
    print("prime_power_table=END")
    print()
    print(f"max_crossing_identity_error={crossing_error:.12e}")
    print(f"max_prime_power_coefficient_error={coefficient_error:.12e}")
    print(f"mixed_prime_readback_error={mixed_readback_error:.12e}")
    hard_errors = (
        owner.moment_residual,
        flow["local_series_error"],
        flow["mixed_log_derivative_error"],
        flow["mixed_integrated_additivity_error"],
        crossing_error,
        coefficient_error,
        mixed_readback_error,
    )
    passed = max(hard_errors) <= args.tolerance
    verdict = "PASS" if passed else "FAIL"
    print(f"flow_log_series={verdict}")
    print(f"crossing_pair_identity={verdict}")
    print(f"m1_m2_m3_coefficient={verdict}")
    print(f"mixed_prime_additivity={verdict}")
    print(f"same_owner_readback={verdict}")
    print("global_spectral_nonnegativity=OPEN")
    print("RH=UNPROVED")

    if not passed:
        raise SystemExit(
            "coefficient-owner screen failed: "
            f"max_error={max(hard_errors):.3e} > tolerance={args.tolerance:.3e}"
        )


if __name__ == "__main__":
    main()
