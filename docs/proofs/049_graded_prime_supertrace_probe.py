#!/usr/bin/env python3
"""Reproduce the local graded-prime supertrace obstruction.

The even/odd jumps cancel the forced diagonal exactly, but their supertrace is
-w(U+U*), whose Fourier symbol changes sign.  A finite cyclic translation
model also shows that every nonzero zero-diagonal prime polynomial has trace
zero and hence cannot be positive semidefinite.
"""

from __future__ import annotations

import argparse
import math


def local_mode_energy(weight: float, theta: float) -> tuple[float, float, float]:
    even = weight * (1.0 - math.cos(theta))
    odd = weight * (1.0 + math.cos(theta))
    return even, odd, even - odd


def cyclic_spectrum(
    size: int, weighted_shifts: list[tuple[float, int]]
) -> list[float]:
    return [
        -2.0
        * sum(
            weight * math.cos(2.0 * math.pi * mode * shift / size)
            for weight, shift in weighted_shifts
        )
        for mode in range(size)
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=127)
    parser.add_argument("--weight", type=float, default=1.0)
    parser.add_argument(
        "--shifts",
        default="1:1,0.7:5,0.4:17",
        help="comma-separated weight:shift pairs for the cyclic probe",
    )
    args = parser.parse_args()

    if args.size < 3:
        raise ValueError("--size must be at least 3")
    if args.weight <= 0:
        raise ValueError("--weight must be positive")

    weighted_shifts: list[tuple[float, int]] = []
    for item in args.shifts.split(","):
        weight_text, shift_text = item.split(":", maxsplit=1)
        weight = float(weight_text)
        shift = int(shift_text) % args.size
        if weight <= 0 or shift == 0:
            raise ValueError("each weight must be positive and each shift nonzero")
        weighted_shifts.append((weight, shift))

    print("local coefficient Gram blocks")
    print(f"G_even = {args.weight / 2:g} * [[1,-1],[-1,1]]")
    print(f"G_odd  = {args.weight / 2:g} * [[1, 1],[ 1,1]]")
    print(f"G_super= [[0,{-args.weight:g}],[{-args.weight:g},0]]")
    print()

    print("local Fourier modes")
    for theta in (0.0, math.pi / 2.0, math.pi):
        even, odd, super_energy = local_mode_energy(args.weight, theta)
        print(
            f"theta={theta:.12g} even={even:+.12g} odd={odd:+.12g} "
            f"super={super_energy:+.12g}"
        )
    print()

    spectrum = cyclic_spectrum(args.size, weighted_shifts)
    trace = sum(spectrum)
    scale = max(1.0, sum(abs(value) for value in spectrum))
    tolerance = 1e-12 * scale

    print("finite cyclic multi-prime probe")
    print(f"size={args.size}")
    print(f"weighted_shifts={weighted_shifts}")
    print(f"min_eigenvalue={min(spectrum):+.16g}")
    print(f"max_eigenvalue={max(spectrum):+.16g}")
    print(f"trace={trace:+.16g}")

    if min(spectrum) >= -tolerance or max(spectrum) <= tolerance:
        raise AssertionError("expected a genuinely indefinite supertrace")
    if abs(trace) > tolerance:
        raise AssertionError("expected the zero-diagonal cyclic operator to be traceless")


if __name__ == "__main__":
    main()
