#!/usr/bin/env python3
"""Record 2127: analytic eighth-order sampling derivative chain.

This replaces the finite-difference pilot in record 2126. The chain is
analytic for the stored Gauss-Legendre seed quadrature: seed derivatives,
cardinal products, P, modulus squares, and W are propagated as truncated
Taylor jets in the real variable xi. It is still a floating diagnostic, not
an interval certificate for the underlying seed integral.
"""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op  # noqa: E402
import fourpoint_coupling_scan_2028 as scan  # noqa: E402
import fourpoint_diagonal_sign_1918 as rig  # noqa: E402

OUTPUT = ROOT / "results" / "2127_routea_n6_analytic_sampling.json"
RHO = complex(0.55, 30.424876125859513)
N_OWNER = 4
N = 6
ORDER = 8
POWER = 10
SEED_SCALE = 0.5
XI_MAX = 75.0
DXI = float(os.environ.get("ROUTEA_DXI", "0.02"))
SEED_ORDER = 300


def series_mul(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    out = np.zeros_like(left)
    for k in range(ORDER + 1):
        out[k] = sum(left[j] * right[k - j]
                     for j in range(k + 1))
    return out


def seed_jet(xi: np.ndarray, nodes: np.ndarray, weights: np.ndarray,
             shift: complex = 0j) -> np.ndarray:
    """Return xi-Taylor coefficients of the powered seed transform."""
    s = 0.5 - 2j * math.pi * xi
    raw = np.empty((ORDER + 1, xi.size), dtype=complex)
    x = SEED_SCALE * nodes
    exponent = np.exp((s[:, None] - shift) * x[None, :])
    for k in range(ORDER + 1):
        raw[k] = np.sum(exponent * (x[None, :] ** k) * weights[None, :], axis=1)
    raw /= np.asarray([math.factorial(k) for k in range(ORDER + 1)])[:, None]
    raw *= np.asarray([(-2j * math.pi) ** k for k in range(ORDER + 1)])[:, None]
    out = np.zeros_like(raw)
    out[0] = 1.0
    for _ in range(POWER):
        out = series_mul(out, raw)
    return out


def node_product_jet(nodes: list[complex], xi: np.ndarray,
                     sign: complex, offset: complex,
                     skip: int | None = None) -> np.ndarray:
    """Taylor coefficients of prod(offset + sign*xi - z) in xi."""
    out = np.zeros((ORDER + 1, xi.size), dtype=complex)
    out[0] = 1.0
    for index, z in enumerate(nodes):
        if index == skip:
            continue
        factor = np.zeros_like(out)
        factor[0] = offset + sign * xi - z
        factor[1] = sign
        out = series_mul(out, factor)
    return out


def cardinal_jet(nodes: list[complex], values: list[complex], xi: np.ndarray,
                 seed0: complex, seed_nodes: np.ndarray,
                 seed_weights: np.ndarray) -> np.ndarray:
    out = np.zeros((ORDER + 1, xi.size), dtype=complex)
    x = SEED_SCALE * seed_nodes
    for index, (z, value) in enumerate(zip(nodes, values)):
        shifted_weights = seed_weights * np.exp(-z * x)
        seed = seed_jet(xi, seed_nodes, shifted_weights)
        product = node_product_jet(nodes, xi, -2j * math.pi, 0.5,
                                   skip=index)
        denominator = np.prod([z - other for j, other in enumerate(nodes)
                               if j != index])
        term = series_mul(product, seed)
        term *= value / (denominator * seed0)
        out += term
    return out


def modulus_square_jet(value: np.ndarray) -> np.ndarray:
    return series_mul(value, np.conjugate(value))


def p_jet(xi: np.ndarray, nodes: list[complex]) -> np.ndarray:
    out = np.zeros((ORDER + 1, xi.size), dtype=complex)
    out[0] = 1.0
    for node in nodes:
        factor = np.zeros_like(out)
        factor[0] = node + 2j * math.pi * xi
        factor[1] = 2j * math.pi
        out = series_mul(out, factor)
    return out


def main() -> None:
    owner, targets, _radius, _known = op.build_owner(RHO, N_OWNER)
    values = [op.target_value(RHO, z) for z in owner]
    seed_nodes, seed_weights = np.polynomial.legendre.leggauss(SEED_ORDER)
    seed_nodes = 2.0 * seed_nodes
    seed_weights = 2.0 * seed_weights * op.smooth_seed_raw(seed_nodes)
    seed0 = complex(np.sum(seed_weights)) ** POWER
    xi = np.arange(-XI_MAX, XI_MAX + 0.5 * DXI, DXI)

    base = cardinal_jet(targets, [1.0 + 0j] * len(targets), xi,
                        seed0, seed_nodes, seed_weights)
    correction = cardinal_jet(owner, values, xi, seed0,
                               seed_nodes, seed_weights)
    centered = [z - 0.5 for z in op.healthy_targets(RHO)[:4]]
    P = p_jet(xi, centered)
    base_sq = modulus_square_jet(base)
    W = base_sq.copy()
    for _ in range(N):
        W = series_mul(W, base_sq)
    W = series_mul(W, modulus_square_jet(correction))
    fs = (W, series_mul(P, W), series_mul(series_mul(P, P), W))

    def seed_transform(values: np.ndarray) -> np.ndarray:
        values = np.asarray(values, dtype=complex)
        return np.sum(np.exp((SEED_SCALE * values)[:, None] * seed_nodes[None, :])
                      * seed_weights[None, :], axis=1) ** POWER
    axis = 0.5 - 2j * math.pi * xi
    direct_base = op.cardinal_transform(
        targets, [1.0 + 0j] * len(targets), seed0, axis, seed_transform)
    direct_correction = op.cardinal_transform(
        owner, values, seed0, axis, seed_transform)
    direct_w = (np.abs(direct_base) ** (2 * (N + 1)) *
                np.abs(direct_correction) ** 2)
    f0_relative_error = float(np.max(
        np.abs(W[0].real - direct_w) / (np.abs(direct_w) + 1e-300)))
    sigma = rig.sigma_vec(2.0 * math.pi * xi)
    prime_values, prime_logs = scan.fast_prime_powers_up_to(math.exp(16.0))
    route_a, coverage = scan.fft_prime_channel(
        xi, (W[0].real, fs[1][0].real, fs[2][0].real),
        prime_values, prime_logs)
    arch = [float(np.trapezoid(sigma * f[0].real, xi)) for f in fs]
    full = [arch[i] + route_a[i] for i in range(3)]
    determinant = full[0] * full[2] - full[1] ** 2
    weight_sum = float(np.sum(2.0 * np.asarray(prime_logs) /
                              np.sqrt(prime_values)))
    derivative_integrals = [
        float(np.trapezoid(np.abs(math.factorial(ORDER) * f[ORDER].real), xi))
        for f in fs]
    sampling_errors = [DXI ** ORDER / math.factorial(ORDER) * value
                       * weight_sum for value in derivative_integrals]
    ec, eb, ed = sampling_errors
    determinant_error = ((abs(full[2]) * ec + abs(full[0]) * ed + ec * ed) +
                         (2.0 * abs(full[1]) * eb + eb ** 2))
    result = {
        "record": 2127,
        "status": "ANALYTIC-DERIVATIVE-SAMPLING-CANDIDATE",
        "owner": {"rho": [RHO.real, RHO.imag], "N": N_OWNER,
                  "owner_cardinality": len(owner)},
        "n": N,
        "xi": {"min": -XI_MAX, "max": XI_MAX, "dxi": DXI},
        "prime_book": int(prime_values.size),
        "coverage": coverage,
        "full_route_a": {"C": full[0], "b": full[1], "D": full[2],
                          "det": determinant},
        "f0_relative_error_vs_direct_cardinal": f0_relative_error,
        "derivative_integral_abs_f8": derivative_integrals,
        "sampling_error_bound": {"C": ec, "b": eb, "D": ed},
        "determinant_error_bound": determinant_error,
        "determinant_margin_ratio": abs(determinant) / determinant_error,
        "nonclaims": [
            "stored Gauss-Legendre seed quadrature is not interval-certified",
            "DFT forward rounding and finite-window tail are not charged",
            "owner is a known-zero under-approximation",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "source": "results/2126_routea_n6_sampling_remainder_screen.json"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
