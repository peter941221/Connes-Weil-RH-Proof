#!/usr/bin/env python3
"""Probe the persistent p=2, m=2 same-square defect.

The endpoint metric Sonin owner has one excess copy of the second prime-power
atom.  For a real compactly supported smooth test h, its same-square value is

    p^(-1) log(p) * (F_h(2 log p) + F_h(-2 log p)),

where F_h is the autocorrelation of h.  This probe uses a normalized C-infinity
bump and verifies that the excess converges to a nonzero value as the physical
grid is refined.  It is numerical confirmation of the exact coefficient
calculation in proof 042, not a substitute for that calculation.
"""

import math

import numpy as np


def smooth_bump(coordinate: np.ndarray, radius: float) -> np.ndarray:
    scaled = coordinate / radius
    result = np.zeros_like(coordinate)
    inside = np.abs(scaled) < 1.0
    result[inside] = np.exp(-1.0 / (1.0 - np.square(scaled[inside])))
    return result


def shifted_values(
    coordinate: np.ndarray, radius: float, shift: float
) -> np.ndarray:
    return smooth_bump(coordinate + shift, radius)


def run_probe() -> None:
    prime = 2.0
    shift = 2.0 * math.log(prime)
    radius = 2.0
    domain_radius = radius + shift + 0.25

    print("points norm_error autocorrelation excess_atom")
    for points in (2**12, 2**13, 2**14, 2**15, 2**16, 2**17):
        coordinate = np.linspace(-domain_radius, domain_radius, points + 1)
        test = smooth_bump(coordinate, radius)
        norm_squared = np.trapz(np.square(test), coordinate)
        test /= math.sqrt(norm_squared)

        shifted = shifted_values(coordinate, radius, shift) / math.sqrt(
            norm_squared
        )
        autocorrelation = np.trapz(test * shifted, coordinate)
        normalized_norm = np.trapz(np.square(test), coordinate)
        excess_atom = (
            2.0 * math.log(prime) / prime * autocorrelation
        )

        print(
            f"{points:7d} {abs(normalized_norm - 1.0):.3e} "
            f"{autocorrelation:.12e} {excess_atom:.12e}"
        )


if __name__ == "__main__":
    run_probe()
