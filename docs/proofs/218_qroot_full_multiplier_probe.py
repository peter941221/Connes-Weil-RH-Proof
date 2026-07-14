#!/usr/bin/env python3
"""FFT screen for the correctly owned full-multiplier Q-root form.

On the source root ``g = (d/dx + 1/2) xi``, and before inserting the ordinary
compact kernel, the noncompact relative form is

    <g, ell_CC20(D) g> + 2 ||L^{-1} g||^2 - <g, K_c g>.

The multiplier is applied to the zero extension of ``g`` by a padded FFT.
Its delta-transform component is sampled on the matching frequency grid by a
DCT of the explicit CC20 function ``delta(exp(x))``.  This is a feasibility
probe, not an interval or discretization certificate.
"""

from __future__ import annotations

import argparse
from importlib import import_module
import math

import numpy as np
from scipy.fft import dct, fft, ifft, fftfreq
from scipy.linalg import null_space
from scipy.sparse.linalg import LinearOperator, eigsh
from scipy.special import digamma, sici


principal_probe = import_module("215_all_prime_principal_form_probe")
qroot_probe = import_module("217_qroot_same_object_relative_probe")


def sine_integral_quotient(argument: np.ndarray) -> np.ndarray:
    result = np.empty_like(argument)
    small = np.abs(argument) < 1e-7
    result[small] = 1 - argument[small] ** 2 / 18
    result[~small] = sici(argument[~small])[0] / argument[~small]
    return result


def delta_log_coordinate(points: np.ndarray) -> np.ndarray:
    rho = np.exp(points)
    plus = 2 * np.pi * (1 + rho)
    minus = 2 * np.pi * (rho - 1)
    return 2 * np.exp(points / 2) * (
        sine_integral_quotient(plus)
        + sine_integral_quotient(minus)
    )


def multiplier_grid(
    physical_mesh: float,
    padding_half_length: float,
    dct_intervals: int,
) -> tuple[np.ndarray, np.ndarray, int]:
    padding_size = int(round(2 * padding_half_length / physical_mesh))
    if padding_size % 2:
        padding_size += 1
    actual_half_length = padding_size * physical_mesh / 2

    delta_points = np.linspace(0, actual_half_length, dct_intervals + 1)
    delta_values = delta_log_coordinate(delta_points)
    delta_mesh = actual_half_length / dct_intervals
    # DCT-I is twice the trapezoidal cosine sum.  The extra factor two in
    # delta_hat(t)=2 integral_0^infinity d(x)cos(tx)dx cancels the half.
    delta_transform = delta_mesh * dct(delta_values, type=1)

    frequencies = 2 * np.pi * fftfreq(padding_size, d=physical_mesh)
    indices = np.rint(
        np.abs(frequencies) * actual_half_length / np.pi
    ).astype(int)
    if int(np.max(indices)) > dct_intervals:
        raise ValueError("DCT grid does not cover the FFT Nyquist frequency")

    two_theta_prime = -np.log(np.pi) + np.real(
        digamma(0.25 + 0.5j * frequencies)
    )
    multiplier = two_theta_prime + delta_transform[indices]
    return multiplier, two_theta_prime, padding_size


def run_cutoff(
    cutoff: int,
    size: int,
    padding_half_length: float,
    dct_intervals: int,
) -> None:
    points, _, _, prime_operator, term_count = (
        principal_probe.build_principal_form(cutoff, size)
    )
    mesh = math.log(cutoff) / (size + 1)
    inverse = qroot_probe.volterra_qroot_inverse(points, mesh)
    multiplier, two_theta_prime, padding_size = multiplier_grid(
        mesh, padding_half_length, dct_intervals
    )

    def spectral_apply(
        vector: np.ndarray, spectral_multiplier: np.ndarray
    ) -> np.ndarray:
        padded = np.zeros(padding_size, dtype=np.complex128)
        padded[:size] = vector
        transformed = fft(padded)
        applied = ifft(spectral_multiplier * transformed).real
        return applied[:size]

    def multiplier_apply(vector: np.ndarray) -> np.ndarray:
        return spectral_apply(vector, multiplier)

    def theta_apply(vector: np.ndarray) -> np.ndarray:
        return spectral_apply(vector, two_theta_prime)

    mean = np.ones_like(points)
    rows = np.vstack(
        (mean, np.cosh(points / 2), np.sinh(points / 2))
    )
    basis = null_space(rows)

    def full_apply(vector: np.ndarray) -> np.ndarray:
        return (
            multiplier_apply(vector)
            + 2 * inverse.T @ (inverse @ vector)
            - prime_operator @ vector
        )

    def compressed_apply(coordinates: np.ndarray) -> np.ndarray:
        return basis.T @ full_apply(basis @ coordinates)

    def weil_apply(vector: np.ndarray) -> np.ndarray:
        # The delta part of ell_CC20 cancels exactly with
        # -D_infinity = 2 Id-K_I after g=L xi.
        return theta_apply(vector) - prime_operator @ vector

    def weil_compressed_apply(coordinates: np.ndarray) -> np.ndarray:
        return basis.T @ weil_apply(basis @ coordinates)

    compressed = LinearOperator(
        (basis.shape[1], basis.shape[1]),
        matvec=compressed_apply,
        dtype=np.float64,
    )
    values, vectors = eigsh(
        compressed, k=1, which="SA", tol=1e-10, maxiter=5000
    )
    weil_compressed = LinearOperator(
        (basis.shape[1], basis.shape[1]),
        matvec=weil_compressed_apply,
        dtype=np.float64,
    )
    weil_values, weil_vectors = eigsh(
        weil_compressed, k=1, which="SA", tol=1e-10, maxiter=5000
    )
    source_root = basis @ vectors[:, 0]
    source_root /= np.linalg.norm(source_root)
    multiplier_value = float(source_root @ multiplier_apply(source_root))
    inverse_value = float(2 * np.linalg.norm(inverse @ source_root) ** 2)
    prime_value = float(source_root @ prime_operator @ source_root)
    weil_root = basis @ weil_vectors[:, 0]
    weil_root /= np.linalg.norm(weil_root)
    theta_value = float(weil_root @ theta_apply(weil_root))
    weil_prime_value = float(weil_root @ prime_operator @ weil_root)

    print(
        f"cutoff={cutoff} size={size} prime_power_terms={term_count} "
        f"padding_size={padding_size}"
    )
    print(
        f"  minimum={values[0]:.12f} "
        f"ell={multiplier_value:.12f} "
        f"two_inverse={inverse_value:.12f} "
        f"prime={prime_value:.12f}"
    )
    print(
        f"  with_KI_minimum={weil_values[0]:.12f} "
        f"two_theta={theta_value:.12f} "
        f"prime={weil_prime_value:.12f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cutoff", type=int, nargs="+", default=[16, 64, 256, 1024]
    )
    parser.add_argument("--size", type=int, default=300)
    parser.add_argument("--padding-half-length", type=float, default=64.0)
    parser.add_argument("--dct-intervals", type=int, default=65536)
    args = parser.parse_args()
    for cutoff in args.cutoff:
        run_cutoff(
            cutoff,
            args.size,
            args.padding_half_length,
            args.dct_intervals,
        )


if __name__ == "__main__":
    main()
