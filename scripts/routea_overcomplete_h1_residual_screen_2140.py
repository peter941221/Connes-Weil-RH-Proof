#!/usr/bin/env python3
"""Record 2140: overcomplete H1-basis residual screen."""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_actual_owner_1980 as owner  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402

OUTPUT = ROOT / "results" / "2140_routea_overcomplete_h1_residual_screen.json"
RHO = complex(0.945, 39.25244858548658)
K = 30.0
N = 0


def known_zeros_in_ball(radius: float, max_index: int = 100) -> list[complex]:
    result: list[complex] = []
    mp.mp.dps = 60
    for index in range(1, max_index + 1):
        zero = mp.zetazero(index)
        if float(mp.im(zero)) - RHO.imag > radius + 1.0:
            break
        point = complex(float(mp.re(zero)), float(mp.im(zero)))
        if abs(point - RHO) <= radius + 1e-10 and not any(abs(point - old) < 1e-10 for old in result):
            result.append(point)
    return result


def constrained_h1(matrix: np.ndarray, gram: np.ndarray, values: np.ndarray) -> tuple[np.ndarray, dict]:
    eigenvalues, eigenvectors = np.linalg.eigh((gram + gram.conj().T) / 2.0)
    floor = max(float(eigenvalues.max()) * 1e-12, 1e-24)
    inverse = (eigenvectors / np.maximum(eigenvalues, floor)) @ eigenvectors.conj().T
    schur = matrix @ inverse @ matrix.conj().T
    coeff = inverse @ matrix.conj().T @ np.linalg.solve(schur, values)
    return coeff, {
        "constraint_resid": float(np.max(np.abs(matrix @ coeff - values))),
        "gram_condition": float(eigenvalues.max() / max(abs(eigenvalues).min(), 1e-300)),
        "coefficient_norm": float(np.sqrt(max(np.real(coeff.conj() @ gram @ coeff), 0.0))),
    }


def family_for_scheme(rho: complex, factors: list[float]) -> list[tuple[float, float]]:
    base = density.design_family(rho, 1.0)
    return [(factor * a, theta) for factor in factors for a, theta in base]


def main() -> None:
    targets = density.target_nodes(RHO)
    target_values = np.asarray([density.target_value(RHO, z) for z in targets], dtype=complex)
    radius = owner.formal_radius(RHO, N)
    omitted = known_zeros_in_ball(radius)
    seed_data = {}
    schemes = (
        ("16_profile", [0.70, 1.00]),
        ("24_profile", [0.55, 0.80, 1.05]),
        ("40_profile_a", [0.40, 0.60, 0.80, 1.00, 1.20]),
        ("40_profile_b", [0.45, 0.65, 0.85, 1.05, 1.25]),
        ("40_profile_c", [0.50, 0.70, 0.90, 1.10, 1.30]),
        ("48_profile", [0.35, 0.55, 0.75, 0.95, 1.15, 1.35]),
    )
    for scheme, factors in schemes:
        fam = family_for_scheme(RHO, factors)
        xw = [density.phi_weights(a, panels=6, m=400) for a, _theta in fam]
        matrix = density.family_values(fam, K, np.asarray(targets, dtype=complex), xw).T
        gram = health.h1_gram(fam)
        base, base_info = constrained_h1(matrix, gram, np.ones(len(targets), dtype=complex))
        corr, corr_info = constrained_h1(matrix, gram, target_values)

        def raw_value(z: complex) -> complex:
            values = density.family_values(fam, K, np.asarray([z], dtype=complex), xw)[:, 0]
            return (base @ values) ** (N + 1) * (corr @ values)

        def square_value(z: complex) -> complex:
            return np.conj(raw_value(1.0 - np.conj(z))) * raw_value(z)

        terms = [square_value(z) for z in omitted]
        xi = np.linspace(-40.0, 40.0, 20001)
        with np.errstate(over="ignore", invalid="ignore"):
            weight, _lb, _lc, _ratio = completion.owner_density(
                targets, fam, K, N, xi, xw, (base, corr)
            )
            polynomial = np.real(density.P_from_nodes(
                xi, completion.counterpart_nodes(RHO)
            ))
            gate = density.gate_entries(
                xi, weight, polynomial, max(a for a, _theta in fam) * (N + 2)
            )
            spread = density.route_spread(gate)
            c_value = float(gate["C"])
            b_value = float(gate["B01"])
            d_value = float(gate["D"])
            determinant = c_value * d_value - b_value * b_value
        seed_data[scheme] = {
            "profile_count": len(fam),
            "factors": factors,
            "support": max(a for a, _theta in fam),
            "base": base_info,
            "correction": corr_info,
            "known_omitted_zero_count": len(omitted),
            "signed_residual_real": float(sum(value.real for value in terms)),
            "absolute_residual_budget": float(sum(abs(value) for value in terms)),
            "residual_over_anchor": float(sum(abs(value) for value in terms)),
            "gate": {
                "C": c_value,
                "B01": b_value,
                "D": d_value,
                "det": determinant,
                "healthy_signs": bool(c_value > 0.0 and d_value < 0.0 and determinant < 0.0),
                "route_spread": [float(value) for value in spread],
                "routes": sorted(gate["prime"].keys()),
                "n_primes": int(gate["n_primes"]),
            },
        }

    result = {
        "record": 2140,
        "status": "OVERCOMPLETE-H1-RESIDUAL-SCREEN",
        "owner_model": "exact orbit/healthy target constraints; known zeta zeros omitted",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "formal_radius": radius,
        "anchor_multiplicity_model": 1.0,
        "schemes": seed_data,
        "nonclaims": [
            "known zeros are a finite under-approximation",
            "H1 Gram is numerical quadrature, not an interval certificate",
            "no abstract-owner residual bound",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "prior_no_go": "results/2139_routea_owner_local_residual_screen.json",
            "basis_gram": "scripts/routea_health_cone_2006.py",
            "family": "scripts/fourpoint_owner_density_1959.py",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
