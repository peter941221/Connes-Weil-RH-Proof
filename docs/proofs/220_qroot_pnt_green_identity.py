#!/usr/bin/env python3
"""Check the correct-Q-root PNT Green-kernel identity.

For a compactly supported smooth pre-root xi, set

    L = d/dx + 1/2,
    g = L xi,
    k0(x, y) = exp(abs(x-y)/2).

The exact distributional calculation gives

    <g, K0 g> = -||xi||_2^2.

This script checks convergence of the two sides for modulated smooth bumps,
verifies the Mellin-row transport M_s(L xi)=(1/2-s)M_s(xi), and reports the
exact finite-prime/PNT-defect split for one cutoff.  It is a numerical sanity
check; the proof is the integration-by-parts argument in the companion note.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def parse_csv_numbers(raw: str, converter):
    return [converter(item.strip()) for item in raw.split(",") if item.strip()]


def is_prime(candidate: int) -> bool:
    if candidate < 2:
        return False
    return all(
        candidate % divisor
        for divisor in range(2, math.isqrt(candidate) + 1)
    )


def prime_powers_below(cutoff: int) -> list[tuple[int, int, int]]:
    terms = []
    for prime in range(2, cutoff):
        if not is_prime(prime):
            continue
        power = prime
        exponent = 1
        while power < cutoff:
            terms.append((power, prime, exponent))
            power *= prime
            exponent += 1
    return sorted(terms)


def bump_and_l_root(
    points: np.ndarray, support_radius: float, modulation: float
) -> tuple[np.ndarray, np.ndarray]:
    bump = np.zeros(points.shape, dtype=float)
    derivative = np.zeros(points.shape, dtype=float)
    inside = np.abs(points) < support_radius
    scaled = points[inside] / support_radius
    denominator = 1.0 - scaled * scaled
    bump[inside] = np.exp(-1.0 / denominator)
    derivative[inside] = (
        bump[inside]
        * (-2.0 * points[inside] / support_radius**2)
        / denominator**2
    )

    phase = np.exp(1j * modulation * points)
    xi = phase * bump
    g = phase * (derivative + (0.5 + 1j * modulation) * bump)
    return xi, g


def l_root_at(
    points: np.ndarray, support_radius: float, modulation: float
) -> np.ndarray:
    return bump_and_l_root(points, support_radius, modulation)[1]


def inner_product(left: np.ndarray, right: np.ndarray, step: float) -> complex:
    return step * np.vdot(left, right)


def green_form(points: np.ndarray, g: np.ndarray, step: float) -> complex:
    kernel = np.exp(0.5 * np.abs(points[:, None] - points[None, :]))
    return step * step * np.vdot(g, kernel @ g)


def finite_prime_form(
    points: np.ndarray,
    g: np.ndarray,
    step: float,
    support_radius: float,
    modulation: float,
    cutoff: int,
) -> tuple[complex, int]:
    value = 0.0j
    terms = prime_powers_below(cutoff)
    for power, prime, _ in terms:
        shift = math.log(power)
        weight = math.log(prime) / math.sqrt(power)
        translated_forward = l_root_at(
            points - shift, support_radius, modulation
        )
        translated_reverse = l_root_at(
            points + shift, support_radius, modulation
        )
        value += weight * inner_product(
            g, translated_forward + translated_reverse, step
        )
    return value, len(terms)


def mellin_row(
    points: np.ndarray, vector: np.ndarray, step: float, coordinate: float
) -> complex:
    return step * np.sum(np.exp(coordinate * points) * vector)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="501,1001,2001")
    parser.add_argument("--modulations", default="0,3,11")
    parser.add_argument("--domain-radius", type=float, default=4.0)
    parser.add_argument("--support-radius", type=float, default=3.0)
    parser.add_argument("--cutoff", type=int, default=512)
    parser.add_argument("--max-relative-error", type=float, default=5e-4)
    args = parser.parse_args()

    sizes = parse_csv_numbers(args.sizes, int)
    modulations = parse_csv_numbers(args.modulations, float)
    if math.log(args.cutoff) <= 2.0 * args.support_radius:
        raise ValueError("cutoff log must exceed the support diameter")

    print("identity=<L xi,K0 L xi>=-||xi||^2")
    print(f"domain_radius={args.domain_radius}")
    print(f"support_radius={args.support_radius}")
    print(f"cutoff={args.cutoff}")

    finest_errors = []
    for modulation in modulations:
        print(f"modulation={modulation:g}")
        previous_error = None
        finest_data = None
        for size in sizes:
            points = np.linspace(-args.domain_radius, args.domain_radius, size)
            step = float(points[1] - points[0])
            xi, g = bump_and_l_root(
                points, args.support_radius, modulation
            )
            norm_sq = inner_product(xi, xi, step).real
            main_form = green_form(points, g, step).real
            absolute_error = abs(main_form + norm_sq)
            relative_error = absolute_error / norm_sq
            ratio = (
                previous_error / relative_error
                if previous_error is not None and relative_error > 0
                else float("nan")
            )
            print(
                f"  size={size} main_form={main_form:.15g} "
                f"norm_sq={norm_sq:.15g} "
                f"relative_error={relative_error:.6e} "
                f"refinement_ratio={ratio:.3f}"
            )
            previous_error = relative_error
            finest_data = (points, step, xi, g, main_form, norm_sq)

        assert finest_data is not None
        points, step, xi, g, main_form, norm_sq = finest_data
        finest_errors.append(abs(main_form + norm_sq) / norm_sq)

        for coordinate in (-0.5, 0.0, 0.5):
            left = mellin_row(points, g, step, coordinate)
            right = (0.5 - coordinate) * mellin_row(
                points, xi, step, coordinate
            )
            row_error = abs(left - right) / max(1.0, abs(right))
            print(
                f"  mellin_s={coordinate:+.1f} "
                f"left={left.real:+.8e}{left.imag:+.8e}j "
                f"right={right.real:+.8e}{right.imag:+.8e}j "
                f"relative_error={row_error:.3e}"
            )

        prime_form, channel_count = finite_prime_form(
            points,
            g,
            step,
            args.support_radius,
            modulation,
            args.cutoff,
        )
        defect_form = prime_form.real - main_form
        reconstructed = main_form + defect_form
        print(
            f"  prime_power_channels={channel_count} "
            f"finite_prime_form={prime_form.real:.12g} "
            f"pnt_defect_form={defect_form:.12g} "
            f"defect_over_norm={defect_form/norm_sq:.12g} "
            f"split_error={abs(reconstructed-prime_form.real):.3e}"
        )

    worst_error = max(finest_errors)
    print(f"worst_finest_relative_error={worst_error:.6e}")
    if worst_error > args.max_relative_error:
        raise RuntimeError("Green-kernel identity did not converge sufficiently")
    print("certificate=PASS")


if __name__ == "__main__":
    main()
