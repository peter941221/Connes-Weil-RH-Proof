#!/usr/bin/env python3
"""Record 2141: search the overcomplete H1 null fibre for a healthy gate."""

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

OUTPUT = ROOT / "results" / "2141_routea_overcomplete_h1_fibre_search.json"
RHO = complex(0.945, 39.25244858548658)
K = 30.0
N = 0
FACTORS = [0.50, 0.70, 0.90, 1.10, 1.30]
SEED = 2141


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


def constrained_h1(matrix: np.ndarray, gram: np.ndarray, values: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh((gram + gram.conj().T) / 2.0)
    floor = max(float(eigenvalues.max()) * 1e-12, 1e-24)
    inverse = (eigenvectors / np.maximum(eigenvalues, floor)) @ eigenvectors.conj().T
    schur = matrix @ inverse @ matrix.conj().T
    return inverse @ matrix.conj().T @ np.linalg.solve(schur, values)


def normalize(vector: np.ndarray, gram: np.ndarray) -> np.ndarray:
    norm = math.sqrt(max(float(np.real(vector.conj() @ gram @ vector)), 1e-300))
    return vector / norm


def main() -> None:
    targets = density.target_nodes(RHO)
    target_values = np.asarray([density.target_value(RHO, z) for z in targets], dtype=complex)
    radius = owner.formal_radius(RHO, N)
    omitted = known_zeros_in_ball(radius)
    base_family = density.design_family(RHO, 1.0)
    fam = [(factor * a, theta) for factor in FACTORS for a, theta in base_family]
    xw = [density.phi_weights(a, panels=6, m=400) for a, _theta in fam]
    matrix = density.family_values(fam, K, np.asarray(targets, dtype=complex), xw).T
    gram = health.h1_gram(fam)
    base0 = constrained_h1(matrix, gram, np.ones(len(targets), dtype=complex))
    corr0 = constrained_h1(matrix, gram, target_values)
    _u, singular, vh = np.linalg.svd(matrix)
    rank = int(np.sum(singular > 1e-10 * singular[0]))
    null = vh[rank:].conj().T
    rng = np.random.default_rng(SEED)
    directions = []
    for _ in range(24):
        direction = null @ (rng.normal(size=null.shape[1]) + 1j * rng.normal(size=null.shape[1]))
        directions.append(normalize(direction, gram))

    xi = np.linspace(-40.0, 40.0, 4001)
    dxi = float(xi[1] - xi[0])
    sig = density.rig.sigma_vec(2.0 * np.pi * xi)
    pset = density.rig.prime_powers_up_to(math.exp(max(a for a, _theta in fam) * (N + 2)))
    kernel = sig.copy()
    for number, weight in pset:
        kernel += 2.0 * weight / math.sqrt(number) * np.cos(2.0 * np.pi * xi * math.log(number))
    polynomial = np.real(density.P_from_nodes(xi, completion.counterpart_nodes(RHO)))

    def evaluate(base: np.ndarray, corr: np.ndarray) -> dict:
        values = density.family_values(fam, K, 0.5 - 2j * np.pi * xi, xw)
        lb = base @ values
        lc = corr @ values
        weight = np.abs(lb) ** (2 * (N + 1)) * np.abs(lc) ** 2
        moments = [float(np.trapezoid(kernel * factor * weight, xi)) for factor in (1.0, polynomial, polynomial * polynomial)]
        c_value, b_value, d_value = moments
        determinant = c_value * d_value - b_value * b_value

        def raw_value(z: complex) -> complex:
            point = density.family_values(fam, K, np.asarray([z], dtype=complex), xw)[:, 0]
            return (base @ point) ** (N + 1) * (corr @ point)

        residual = sum(abs(np.conj(raw_value(1.0 - np.conj(z))) * raw_value(z)) for z in omitted)
        return {"C": c_value, "B01": b_value, "D": d_value, "det": determinant, "residual": float(residual), "healthy": bool(c_value > 0 and d_value < 0 and determinant < 0)}

    candidates = []
    for trial in range(240):
        direction_base = directions[trial % len(directions)]
        direction_corr = directions[(7 * trial + 3) % len(directions)]
        scale_base = float(np.sign(rng.normal()) * 10 ** rng.uniform(-1.0, 1.0))
        scale_corr = float(np.sign(rng.normal()) * 10 ** rng.uniform(-1.0, 1.0))
        reading = evaluate(base0 + scale_base * direction_base, corr0 + scale_corr * direction_corr)
        if reading["healthy"] or len(candidates) < 5:
            candidates.append({"trial": trial, "scale_base": scale_base, "scale_corr": scale_corr, **reading})
    candidates.sort(key=lambda row: (not row["healthy"], row["residual"]))
    result = {
        "record": 2141,
        "status": "OVERCOMPLETE-H1-FIBRE-SEARCH",
        "owner_model": "exact orbit/healthy target constraints; known zeta zeros omitted",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "factors": FACTORS,
        "profile_count": len(fam),
        "nullity": int(null.shape[1]),
        "known_omitted_zero_count": len(omitted),
        "search": {"seed": SEED, "trials": 240, "xi_points": len(xi), "prime_count": len(pset)},
        "best_candidates": candidates[:20],
        "nonclaims": [
            "direct kernel grid is a screen, not an interval certificate",
            "known zeros are a finite under-approximation",
            "no uniform owner transfer",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "results/2140_routea_overcomplete_h1_residual_screen.json",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
