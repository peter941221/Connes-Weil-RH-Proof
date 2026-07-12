#!/usr/bin/env python3
"""Construct pole-neutral narrow-bump tests with zero prime-ratio overlaps."""

import math

import numpy as np


def bump(coordinate: np.ndarray, center: float, radius: float) -> np.ndarray:
    scaled = (coordinate - center) / radius
    values = np.zeros_like(coordinate)
    inside = np.abs(scaled) < 1.0
    values[inside] = np.exp(-1.0 / (1.0 - scaled[inside] ** 2))
    return values


def run_probe() -> None:
    centers = np.array([0.05, 0.52, 1.12, 1.75])
    radius = 0.01
    coordinate = np.linspace(0.0, 1.80, 100001)
    basis = np.array([bump(coordinate, center, radius) for center in centers])

    # Three representative real pole rows: mass and the two half-point rows.
    pole_rows = np.array(
        [
            np.trapz(basis, coordinate, axis=1),
            np.trapz(basis * np.cosh(coordinate / 2.0), coordinate, axis=1),
            np.trapz(basis * np.sinh(coordinate / 2.0), coordinate, axis=1),
        ]
    )
    _, _, vh = np.linalg.svd(pole_rows)
    coefficients = vh[-1]
    test = coefficients @ basis

    differences = {
        math.log(3.0 / 2.0),
        math.log(5.0 / 3.0),
        math.log(5.0 / 2.0),
    }
    residuals = pole_rows @ coefficients
    print("pole_residual_norm", np.linalg.norm(residuals))
    print("test_norm", math.sqrt(float(np.trapz(test * test, coordinate))))
    print("support_width", centers[-1] - centers[0] + 2.0 * radius)
    for difference in sorted(differences):
        print(
            "autocorrelation",
            difference,
            np.trapz(
                test
                * np.interp(
                    coordinate + difference,
                    coordinate,
                    test,
                    left=0.0,
                    right=0.0,
                ),
                coordinate,
            ),
        )


if __name__ == "__main__":
    run_probe()
