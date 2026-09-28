#!/usr/bin/env python3
"""Record 2139: screen omitted low-shell residual for an owner-local prefix."""

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

OUTPUT = ROOT / "results" / "2139_routea_owner_local_residual_screen.json"
RHO = complex(0.945, 39.25244858548658)
N = 0


def known_zeros_in_ball(radius: float, max_index: int = 100) -> list[complex]:
    result: list[complex] = []
    mp.mp.dps = 60
    center = mp.mpc(RHO.real, RHO.imag)
    for index in range(1, max_index + 1):
        zero = mp.zetazero(index)
        if float(mp.im(zero)) - RHO.imag > radius + 1.0:
            break
        for point in (complex(float(mp.re(zero)), float(mp.im(zero))),
                      complex(float(mp.re(zero)), -float(mp.im(zero)))):
            if abs(point - RHO) <= radius + 1e-10 and not any(abs(point - old) < 1e-10 for old in result):
                result.append(point)
    return result


def main() -> None:
    targets = owner.healthy_targets(RHO)
    target_values = [owner.target_value(RHO, z) for z in targets]
    radius = owner.formal_radius(RHO, N)
    seed0 = complex(owner.quadrature_seed_transform(np.array([0j]))[0])
    seed_transform = lambda s: owner.quadrature_seed_transform(s)

    omitted = known_zeros_in_ball(radius)
    def screen(prefix_count: int) -> dict:
        prefix = omitted[:prefix_count]
        nodes = targets + prefix
        values = target_values + [0j] * len(prefix)

        def raw_value(z: complex) -> complex:
            s = np.array([z], dtype=complex)
            base = owner.cardinal_transform(nodes, [1.0 + 0j] * len(nodes), seed0, s, seed_transform)[0]
            correction = owner.cardinal_transform(nodes, values, seed0, s, seed_transform)[0]
            return base ** (N + 1) * correction

        def square_value(z: complex) -> complex:
            return np.conj(raw_value(1.0 - np.conj(z))) * raw_value(z)

        remaining = omitted[prefix_count:]
        contributions = [{"zero": [z.real, z.imag], "term": [square_value(z).real, square_value(z).imag], "abs": abs(square_value(z))} for z in remaining]
        residual = sum(item["term"][0] for item in contributions)
        abs_budget = sum(item["abs"] for item in contributions)
        return {"prefix_count": prefix_count, "interpolation_nodes": len(nodes), "remaining_omitted_zero_count": len(remaining), "signed_residual_real": residual, "absolute_residual_budget": abs_budget, "residual_over_anchor": abs_budget}

    sweep = [screen(prefix_count) for prefix_count in (0, 5, 10, 15, len(omitted))]
    result = {
        "record": 2139,
        "status": "OWNER-LOCAL-RESIDUAL-SCREEN",
        "owner_model": "rho-orbit-and-healthy-target interpolation, with a sweep adding known zeros",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "formal_radius": radius,
        "known_omitted_zero_count": len(omitted),
        "anchor_multiplicity_model": 1.0,
        "prefix_sweep": sweep,
        "nonclaims": [
            "known zeta zeros are only a finite under-approximation",
            "quadrature and interpolation are numerical",
            "this does not bound the abstract omitted owner",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "construction": "scripts/fourpoint_actual_owner_1980.py",
            "consumer": "docs/proofs/2138_routea_residual_budget_consumer.md",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
