"""Scaling audit for Proof 347's continuous singular-inner limit.

This checks only the periodic Riemann-sum scaling of equations
(AS.25)--(AS.29).  It is not a finite-section model of the Gate response.
"""

from __future__ import annotations

import argparse
import math


def compact_correlation(u: float, support: float) -> float:
    """A C^3 compact bump used as a root-correlation surrogate."""

    ratio = abs(u) / support
    if ratio >= 1.0:
        return 0.0
    return (1.0 - ratio * ratio) ** 4


def detector_energy(box_length: float, support: float) -> float:
    max_mode = int(math.floor(support * box_length / (2.0 * math.pi)))
    energy = 0.0
    for mode in range(1, max_mode + 1):
        displacement = 2.0 * math.pi * mode / box_length
        coefficient = (
            2.0
            * math.pi
            / box_length
            * compact_correlation(displacement, support)
        )
        energy += mode * coefficient * coefficient
    return energy


def continuum_detector_energy(support: float, steps: int = 200_000) -> float:
    step = support / steps
    total = 0.0
    for index in range(steps):
        displacement = (index + 0.5) * step
        value = compact_correlation(displacement, support)
        total += displacement * value * value
    return total * step


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lengths", default="64,128,256,512,1024")
    parser.add_argument("--frequency", type=float, default=math.log(2.0))
    parser.add_argument("--coefficient", type=float, default=2.0 ** -0.5)
    parser.add_argument("--support", type=float, default=2.0)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    lengths = [float(value) for value in args.lengths.split(",")]
    target_detector_energy = continuum_detector_energy(args.support)
    target_mixed_pairing = (
        2.0
        * args.frequency
        * args.coefficient
        * compact_correlation(args.frequency, args.support)
    )

    print("Proof 347 atomic-singular localization scaling audit")
    print(f"continuum detector energy = {target_detector_energy:.12e}")
    print(f"continuum mixed pairing  = {target_mixed_pairing:.12e}")
    print()
    print(
        "R       z_R          E_f/R        E_w           "
        "UG/sqrt(R)   mixed         mixed_error"
    )

    for box_length in lengths:
        mode = max(1, round(args.frequency * box_length / (2.0 * math.pi)))
        represented_frequency = 2.0 * math.pi * mode / box_length
        background_energy = mode * args.coefficient * args.coefficient
        root_energy = detector_energy(box_length, args.support)
        global_gradient_bound = 4.0 * math.sqrt(
            background_energy * root_energy
        )
        root_coefficient = (
            2.0
            * math.pi
            / box_length
            * compact_correlation(represented_frequency, args.support)
        )
        mixed_pairing = 2.0 * mode * args.coefficient * root_coefficient

        print(
            f"{box_length:5.0f}  "
            f"{represented_frequency: .8f}  "
            f"{background_energy / box_length: .8e}  "
            f"{root_energy: .8e}  "
            f"{global_gradient_bound / math.sqrt(box_length): .8e}  "
            f"{mixed_pairing: .8e}  "
            f"{abs(mixed_pairing - target_mixed_pairing): .3e}"
        )


if __name__ == "__main__":
    main()
