#!/usr/bin/env python3
"""Record 2141 verification: full Route-A gate for selected fibre candidates."""

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

INPUT = ROOT / "results" / "2141_routea_overcomplete_h1_fibre_search.json"
OUTPUT = ROOT / "results" / "2141_routea_overcomplete_h1_fibre_verify.json"
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


def build_fibre():
    targets = density.target_nodes(RHO)
    target_values = np.asarray([density.target_value(RHO, z) for z in targets], dtype=complex)
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
        norm = math.sqrt(max(float(np.real(direction.conj() @ gram @ direction)), 1e-300))
        directions.append(direction / norm)
    metadata = {
        "target_constraint_residual": float(max(np.max(np.abs(matrix @ base0 - 1.0)), np.max(np.abs(matrix @ corr0 - target_values)))),
        "gram_condition": float(np.linalg.cond(gram)),
        "nullity": int(null.shape[1]),
    }
    return fam, xw, base0, corr0, directions, metadata


def evaluate_candidate(fam, xw, base0, corr0, directions, omitted, row, xi_points):
    base_direction = directions[row["trial"] % len(directions)]
    corr_direction = directions[(7 * row["trial"] + 3) % len(directions)]
    base = base0 + row["scale_base"] * base_direction
    corr = corr0 + row["scale_corr"] * corr_direction
    targets = density.target_nodes(RHO)
    target_values = np.asarray([density.target_value(RHO, z) for z in targets], dtype=complex)
    matrix = density.family_values(fam, K, np.asarray(targets, dtype=complex), xw).T
    constraint_residual = float(max(np.max(np.abs(matrix @ base - 1.0)), np.max(np.abs(matrix @ corr - target_values))))
    xi = np.linspace(-40.0, 40.0, xi_points)
    with np.errstate(over="ignore", invalid="ignore"):
        weight, _lb, _lc, ratio = completion.owner_density(targets, fam, K, N, xi, xw, (base, corr))
        polynomial = np.real(density.P_from_nodes(xi, completion.counterpart_nodes(RHO)))
        gate = density.gate_entries(xi, weight, polynomial, max(a for a, _theta in fam) * (N + 2))
    spread = density.route_spread(gate)

    def raw_value(z):
        values = density.family_values(fam, K, np.asarray([z], dtype=complex), xw)[:, 0]
        return (base @ values) ** (N + 1) * (corr @ values)

    residual = float(sum(abs(np.conj(raw_value(1.0 - np.conj(z))) * raw_value(z)) for z in omitted))
    determinant = float(gate["C"] * gate["D"] - gate["B01"] ** 2)
    return {
        "trial": row["trial"], "scale_base": row["scale_base"], "scale_corr": row["scale_corr"],
        "xi_points": xi_points, "constraint_residual": constraint_residual,
        "max_cancellation_ratio": float(np.nanmax(ratio)), "residual": residual,
        "gate": {
            "C": float(gate["C"]), "B01": float(gate["B01"]), "D": float(gate["D"]), "det": determinant,
            "healthy_signs": bool(gate["C"] > 0 and gate["D"] < 0 and determinant < 0),
            "route_key": gate["route_key"], "routes": sorted(gate["prime"].keys()),
            "route_spread": [float(value) for value in spread], "n_primes": int(gate["n_primes"]),
        },
    }


def main() -> None:
    source = json.loads(INPUT.read_text(encoding="utf-8"))
    fam, xw, base0, corr0, directions, metadata = build_fibre()
    omitted = known_zeros_in_ball(owner.formal_radius(RHO, N))
    readings = []
    for row in source["best_candidates"][:3]:
        readings.append({"candidate": row, "refinement": [evaluate_candidate(fam, xw, base0, corr0, directions, omitted, row, points) for points in (4001, 10001, 20001)]})
    result = {
        "record": 2141, "status": "OVERCOMPLETE-H1-FIBRE-VERIFICATION", "owner_model": source["owner_model"],
        "rho": [RHO.real, RHO.imag], "N": N, "known_omitted_zero_count": len(omitted),
        "construction": metadata, "candidates": readings,
        "decision_rule": "healthy requires C > 0, D < 0, det < 0; route spread is reported, not silently discarded",
        "nonclaims": ["finite known-zero set is not the formal closed-ball owner", "H1 Gram and quadrature remain floating-point screens", "no producer theorem, actual-owner transfer, or RH claim"],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)), "input": os.fspath(INPUT.relative_to(ROOT))},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()