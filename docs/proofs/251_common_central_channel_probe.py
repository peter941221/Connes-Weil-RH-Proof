#!/usr/bin/env python3
"""Diagnostic for Proof 251's common archimedean central channel.

The exact survival of the linear central channel is an operator-order
calculation in the accompanying proof document.  This script checks the
archimedean scattering phase, locates resonant critical-line lattice points
with both central signs, and tests a spectral-concentration model.  The
Gaussian envelope in the last test is diagnostic only and is not claimed to
be a compactly supported Yoshida source.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


LANCZOS_COEFFICIENTS = np.array(
    [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278998905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ]
)


def log_gamma_lanczos(values: np.ndarray) -> np.ndarray:
    shifted = values - 1.0
    series = np.full_like(values, LANCZOS_COEFFICIENTS[0], dtype=complex)
    for index, coefficient in enumerate(
        LANCZOS_COEFFICIENTS[1:], start=1
    ):
        series += coefficient / (shifted + index)
    tail = shifted + 7.5
    return (
        0.5 * np.log(2.0 * np.pi)
        + (shifted + 0.5) * np.log(tail)
        - tail
        + np.log(series)
    )


def archimedean_scattering(frequencies: np.ndarray) -> np.ndarray:
    arguments = 0.25 + 0.5j * frequencies
    log_gamma = log_gamma_lanczos(arguments)
    return np.exp(
        -1j * frequencies * math.log(math.pi)
        + log_gamma
        - np.conj(log_gamma)
    )


def central_multiplier(frequencies: np.ndarray) -> np.ndarray:
    # Proof 225's center has k_infinity(0)=2 and the sign in (T.6).
    return -(2.0 / math.pi) * np.real(
        archimedean_scattering(frequencies)
    )


def choose_resonance_integer(
    delta: float, gamma: float, target_contraction: float
) -> int:
    if gamma == 0.0:
        raise ValueError("the diagnostic resonance grid requires gamma != 0")
    integer = 1
    while True:
        shift = 2.0 * math.pi * integer / abs(gamma)
        contraction = 1.0 / math.cosh(shift * abs(delta))
        if contraction <= target_contraction:
            return integer
        integer += 1


def weighted_central_average(
    center: float,
    resonance_shift: float,
    envelope_width: float,
    power: int,
    grid_size: int,
) -> float:
    half_width = max(6.0 * envelope_width, 4.0 * math.pi / resonance_shift)
    points = np.linspace(center - half_width, center + half_width, grid_size)
    gaussian = np.exp(-((points - center) / envelope_width) ** 2)
    resonant = np.abs(np.cos(resonance_shift * points)) ** (2 * power)
    weights = gaussian * resonant
    values = central_multiplier(points)
    return float(np.trapz(weights * values, points) / np.trapz(weights, points))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta", type=float, default=-0.1)
    parser.add_argument("--gamma", type=float, default=14.134725141734695)
    parser.add_argument("--target-contraction", type=float, default=0.45)
    parser.add_argument("--frequency-bound", type=float, default=40.0)
    parser.add_argument("--frequency-grid", type=int, default=20001)
    parser.add_argument("--envelope-width", type=float, default=0.12)
    parser.add_argument("--powers", default="4,8,16,32,64")
    parser.add_argument("--concentration-grid", type=int, default=20001)
    parser.add_argument("--max-unitarity-error", type=float, default=2e-12)
    args = parser.parse_args()

    if args.delta == 0.0:
        raise ValueError("delta must be nonzero")
    if not 0.0 < args.target_contraction < 1.0:
        raise ValueError("target-contraction must lie in (0,1)")
    if args.frequency_bound <= 1.0:
        raise ValueError("frequency-bound must exceed 1")
    if args.frequency_grid < 1001:
        raise ValueError("frequency-grid must be at least 1001")

    resonance_integer = choose_resonance_integer(
        args.delta, args.gamma, args.target_contraction
    )
    resonance_shift = (
        2.0 * math.pi * resonance_integer / abs(args.gamma)
    )
    contraction = 1.0 / math.cosh(
        resonance_shift * abs(args.delta)
    )
    lattice_spacing = math.pi / resonance_shift

    frequencies = np.linspace(
        -args.frequency_bound,
        args.frequency_bound,
        args.frequency_grid,
    )
    scattering = archimedean_scattering(frequencies)
    unitarity_error = float(np.max(np.abs(np.abs(scattering) - 1.0)))
    multiplier = -(2.0 / math.pi) * np.real(scattering)

    max_index = int(args.frequency_bound / lattice_spacing)
    lattice_indices = np.arange(-max_index, max_index + 1)
    lattice = lattice_indices * lattice_spacing
    lattice_values = central_multiplier(lattice)
    positive_indices = np.flatnonzero(lattice_values > 0.2)
    negative_indices = np.flatnonzero(lattice_values < -0.2)
    if len(positive_indices) == 0 or len(negative_indices) == 0:
        raise RuntimeError("resonant lattice did not see both central signs")

    positive_choice = int(positive_indices[np.argmin(np.abs(lattice[positive_indices]))])
    negative_choice = int(negative_indices[np.argmin(np.abs(lattice[negative_indices]))])
    positive_frequency = float(lattice[positive_choice])
    negative_frequency = float(lattice[negative_choice])
    powers = [
        int(item.strip())
        for item in args.powers.split(",")
        if item.strip()
    ]

    print("identity=common archimedean central-channel sign probe")
    print(f"delta={args.delta:.12f} gamma={args.gamma:.12f}")
    print(f"resonance_integer={resonance_integer}")
    print(f"resonance_shift={resonance_shift:.12f}")
    print(f"critical_contraction={contraction:.12e}")
    print(f"resonant_lattice_spacing={lattice_spacing:.12e}")
    print(f"scattering_unitarity_error={unitarity_error:.3e}")
    print(f"sampled_central_min={float(np.min(multiplier)):.12e}")
    print(f"sampled_central_max={float(np.max(multiplier)):.12e}")
    print(
        f"nearest_positive_lattice_frequency={positive_frequency:.12e} "
        f"value={lattice_values[positive_choice]:.12e}"
    )
    print(
        f"nearest_negative_lattice_frequency={negative_frequency:.12e} "
        f"value={lattice_values[negative_choice]:.12e}"
    )
    print("concentration_table=BEGIN")
    for power in powers:
        positive_average = weighted_central_average(
            positive_frequency,
            resonance_shift,
            args.envelope_width,
            power,
            args.concentration_grid,
        )
        negative_average = weighted_central_average(
            negative_frequency,
            resonance_shift,
            args.envelope_width,
            power,
            args.concentration_grid,
        )
        print(
            f"power={power} "
            f"positive_average={positive_average:.12e} "
            f"negative_average={negative_average:.12e}"
        )
    print("concentration_table=END")

    if unitarity_error > args.max_unitarity_error:
        raise RuntimeError("archimedean scattering lost unit modulus")
    if not float(np.min(multiplier)) < -0.2 < 0.2 < float(np.max(multiplier)):
        raise RuntimeError("central multiplier did not exhibit both signs")

    print("certificate=PASS")
    print("common_central_multiplier_indefinite_verdict=PASS")
    print("resonant_lattice_both_signs_verdict=PASS")
    print("compact_source_spectral_steering_verdict=OPEN")
    print("same_object_sign_orientation_verdict=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
