#!/usr/bin/env python3
"""Record 1980: actual-owner under-approximation probe.

This probe is deliberately stricter than record 1959:

* the correction owner contains the known source zeros in the formal closed
  ball, the hypothetical four-point orbit, and all healthy target nodes;
* the base still uses only the healthy target nodes, matching the Lean
  construction;
* the same ``rho``, owner, ``n`` and vertex ``lambda = b / C`` feed the gate
  and the tail diagnostic.

The source-zero set is not computable from the Lean definition.  We therefore
use a reproducible known-zero under-approximation and mark every result as
UNDERAPPROXIMATION.  This is useful as a lower-bound stress test, never as a
GO certificate.
"""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import fourpoint_owner_density_1959 as legacy  # noqa: E402


def smooth_transition(x: np.ndarray | float) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    a = np.zeros_like(x)
    b = np.zeros_like(x)
    ma = x > 0
    mb = (1.0 - x) > 0
    a[ma] = np.exp(-1.0 / x[ma])
    b[mb] = np.exp(-1.0 / (1.0 - x[mb]))
    d = a + b
    out = np.zeros_like(x)
    nz = d > 0
    out[nz] = a[nz] / d[nz]
    return out


def smooth_seed_raw(x: np.ndarray) -> np.ndarray:
    """The committed ``smoothSeedRaw`` from C1ExplicitSmoothSeed.lean."""
    return smooth_transition(x + 2.0) * smooth_transition(2.0 - x)


def quadrature_seed_transform(s: np.ndarray, order: int = 800,
                             chunk: int = 512) -> np.ndarray:
    """Gauss-Legendre evaluation of the committed seed Laplace transform."""
    nodes, weights = np.polynomial.legendre.leggauss(order)
    x = 2.0 * nodes
    w = 2.0 * weights * smooth_seed_raw(x)
    out = np.empty(np.asarray(s).shape, dtype=complex)
    flat = np.asarray(s, dtype=complex).reshape(-1)
    for start in range(0, flat.size, chunk):
        block = flat[start:start + chunk]
        out.reshape(-1)[start:start + chunk] = np.sum(
            np.exp(block[:, None] * x[None, :]) * w[None, :], axis=1
        )
    return out


def dedup(values: list[complex], tol: float = 1e-10) -> list[complex]:
    out: list[complex] = []
    for value in values:
        if not any(abs(value - old) <= tol for old in out):
            out.append(value)
    return out


def healthy_targets(rho: complex) -> list[complex]:
    return dedup([
        rho,
        1.0 - np.conj(rho),
        np.conj(rho),
        1.0 - rho,
        rho + 0.5,
        0.5 + 0j,
        1.0 + 0j,
        1.5 + 0j,
    ])


def target_value(rho: complex, z: complex) -> complex:
    if abs(z - rho) < 1e-10:
        return 1.0 + 0j
    if abs(z - (1.0 - np.conj(rho))) < 1e-10:
        return -1.0 + 0j
    if abs(z - (rho + 0.5)) < 1e-10:
        return -1.0 + 0j
    return 0j


def known_source_zeros_in_ball(rho: complex, radius: float,
                               max_index: int = 200) -> list[complex]:
    """Known upper-half zeta zeros lying in the formal closed ball."""
    result: list[complex] = []
    mp.mp.dps = 60
    center = mp.mpc(rho.real, rho.imag)
    for index in range(1, max_index + 1):
        zero = mp.zetazero(index)
        if float(mp.im(zero)) - rho.imag > radius + 1.0:
            break
        z = complex(float(mp.re(zero)), float(mp.im(zero)))
        if abs(z - rho) <= radius + 1e-10:
            result.append(z)
        # The lower-half conjugate is only included when it is actually in
        # the same ball; this mirrors the metric owner rather than symmetry.
        zc = np.conj(z)
        if abs(zc - rho) <= radius + 1e-10:
            result.append(complex(zc))
    return result


def formal_radius(rho: complex, N: int) -> float:
    return float(2.0 ** (N + 1) + 2.0 + abs(2.0 - rho))


def node_product(nodes: list[complex], z: complex, s: np.ndarray | complex):
    s_arr = np.asarray(s, dtype=complex)
    product = np.ones_like(s_arr, dtype=complex)
    skipped = False
    for node in nodes:
        if not skipped and abs(node - z) <= 1e-10:
            skipped = True
            continue
        product *= node - s_arr
    return product


def cardinal_transform(nodes: list[complex], values: list[complex],
                       seed0: complex, s: np.ndarray,
                       seed_transform: callable) -> np.ndarray:
    s = np.asarray(s, dtype=complex)
    total = np.zeros_like(s, dtype=complex)
    for z, value in zip(nodes, values):
        if abs(value) == 0:
            continue
        denominator = node_product(nodes, z, z) * seed0
        total += (value / denominator) * node_product(nodes, z, s) * \
            seed_transform(s - z)
    return total


def build_owner(rho: complex, N: int) -> tuple[list[complex], list[complex],
                                                float, list[complex]]:
    radius = formal_radius(rho, N)
    known = known_source_zeros_in_ball(rho, radius)
    orbit = [rho, 1.0 - np.conj(rho), np.conj(rho), 1.0 - rho]
    targets = healthy_targets(rho)
    owner = dedup(known + orbit + targets)
    return owner, targets, radius, known


def min_separation(nodes: list[complex]) -> float:
    if len(nodes) < 2:
        return float("inf")
    return min(abs(a - b) for i, a in enumerate(nodes)
               for b in nodes[i + 1:])


def product_summary(rho: complex, owner: list[complex], targets: list[complex]) -> list[dict]:
    rows = []
    for z in targets:
        p = node_product(owner, z, z)
        rows.append({
            "node": [float(z.real), float(z.imag)],
            "target_value_abs": float(abs(target_value(rho, z))),
            "node_product_abs": float(abs(p)),
            "node_product_log10_abs": float(math.log10(max(abs(p), 1e-300))),
        })
    return rows


def decay_scan(base_nodes: list[complex], base_values: list[complex],
               corr_nodes: list[complex], corr_values: list[complex],
               seed0: complex, seed_transform: callable,
               t_max: float = 220.0, nt: int = 441) -> dict:
    ts = np.linspace(0.0, t_max, nt)
    sigmas = np.linspace(0.0, 1.0, 5)
    base_peak = np.zeros_like(ts)
    base_c2 = np.zeros_like(ts)
    corr_c2 = np.zeros_like(ts)
    base_c4 = np.zeros_like(ts)
    for sigma in sigmas:
        s = sigma + 1j * ts
        lb = cardinal_transform(base_nodes, base_values, seed0, s,
                                seed_transform)
        lc = cardinal_transform(corr_nodes, corr_values, seed0, s,
                                seed_transform)
        abs_t = np.abs(ts / (2.0 * math.pi))
        base_peak = np.maximum(base_peak, np.abs(lb))
        base_c2 = np.maximum(base_c2, abs_t ** 2 * np.abs(lb))
        base_c4 = np.maximum(base_c4, abs_t ** 4 * np.abs(lb))
        corr_c2 = np.maximum(corr_c2, abs_t ** 2 * np.abs(lc))
    tail_need = None
    for i in range(nt):
        if np.max(base_peak[i:]) <= 0.5:
            tail_need = float(ts[i])
            break
    return {
        "T_need_grid": tail_need,
        "base_contract_max": float(np.max(base_peak)),
        "base_C2_sup_grid": float(np.max(base_c2)),
        "C4_sup_grid": float(np.max(base_c4)),
        "C2_sup_grid": float(np.max(corr_c2)),
        "t_max": t_max,
        "nt": nt,
    }


def run_case(rho: complex, N: int = 0, n: int = 0,
             xi_max: float = 40.0, dxi: float = 0.01) -> dict:
    owner, targets, radius, known = build_owner(rho, N)
    seed0 = complex(quadrature_seed_transform(np.array([0j]))[0])
    seed_transform = lambda s: quadrature_seed_transform(s)
    base_values = [1.0 + 0j] * len(targets)
    corr_values = [target_value(rho, z) for z in owner]
    xi = np.arange(-xi_max, xi_max + 0.5 * dxi, dxi)
    s_axis = 0.5 - 2j * math.pi * xi
    lb = cardinal_transform(targets, base_values, seed0, s_axis,
                            seed_transform)
    lc = cardinal_transform(owner, corr_values, seed0, s_axis,
                            seed_transform)
    W = np.abs(lb) ** (2 * (n + 1)) * np.abs(lc) ** 2
    centered_orbit = [z - 0.5 for z in healthy_targets(rho)[:4]]
    P = np.real(legacy.P_from_nodes(xi, centered_orbit))
    support_radius = 2.0 * (n + 2)
    gate_error = None
    try:
        gate = legacy.gate_entries(xi, W, P, support_radius)
        C, b, D = gate["C"], gate["B01"], gate["D"]
        determinant = C * D - b * b
        lam = b / C if C != 0 else float("nan")
    except (FloatingPointError, OverflowError, ValueError) as exc:
        gate = None
        gate_error = f"{type(exc).__name__}: {exc}"
        C = b = D = determinant = lam = float("nan")
    decay = decay_scan(targets, base_values, owner, corr_values, seed0,
                       seed_transform)
    H = 3.0 + abs(rho)
    L = H ** 4 * (H ** 4 + abs(lam)) ** 2 * (2.0 * math.pi) ** 12 * (
        (0.5 ** n) * decay["C4_sup_grid"] * decay["C2_sup_grid"]
    ) ** 2
    return {
        "record": 1980,
        "status": ("UNDERAPPROXIMATION_NUMERIC_OVERFLOW"
                   if gate_error else "UNDERAPPROXIMATION_ONLY"),
        "owner_model": "known zeta zeros in formal closed ball + hypothetical orbit + healthy targets",
        "rho": [rho.real, rho.imag],
        "N": N,
        "n": n,
        "radius": radius,
        "known_zero_count": len(known),
        "owner_cardinality": len(owner),
        "target_cardinality": len(targets),
        "min_separation": min_separation(owner),
        "node_products": product_summary(rho, owner, targets),
        "seed_laplace_at_zero": [seed0.real, seed0.imag],
        "xi_grid": {"xi_max": xi_max, "dxi": dxi, "points": int(len(xi))},
        "gate": {
            "C": C,
            "b": b,
            "D": D,
            "det": determinant,
            "lambda": lam,
            "C_positive": C > 0,
            "b_positive": b > 0,
            "det_negative": determinant < 0,
            "route": gate["route_key"] if gate else None,
            "n_primes": gate["n_primes"] if gate else None,
            "error": gate_error,
        },
        "decay_scan": decay,
        "N_selection": {
            "base_Cb_grid": decay["base_C2_sup_grid"],
            "inequality": "Cb^2 * (2*pi)^4 < 2^(4*(N+1))",
            "N_used": N,
            "N_is_formally_certified": False,
            "note": "Cb is a finite-grid numerical envelope only; Lean still needs an analytic bound",
        },
        "tail_proxy": {
            "H": H,
            "L_n": L,
            "lambda_squared": lam * lam,
            "L_over_lambda_sq": L / (lam * lam) if lam != 0 else float("inf"),
            "note": "beta_s and xiMultiplicity remain formal-owner inputs; this is not the Lean tail ratio",
        },
        "provenance": [
            "ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean",
            "ConnesWeilRH/Dev/C1ExplicitSmoothSeed.lean",
            "ConnesWeilRH/Dev/C1ExplicitFiniteNodeCorrection.lean",
            "known zeros supplied by mpmath.zetazero; not a proof of the full source owner",
        ],
    }


TARGET_RHO = complex(0.55, 14.134725141734693)


def main() -> None:
    output = ROOT / "results" / "1980_actual_owner_underapprox.json"
    # The old N=0 probe is not admissible for this height.  On the committed
    # smoothSeed cardinal base, the finite-grid Cb envelope is about 4.1e4;
    # the displayed height-budget inequality first passes at N=10.  We report
    # N=10 as the least-grid-admissible stress case, while keeping the result
    # explicitly non-certifying.
    report = run_case(TARGET_RHO, N=10)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
