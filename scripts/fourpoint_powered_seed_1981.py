#!/usr/bin/env python3
"""Record 1981: reproducible powered-seed same-index screen.

The changed assumption is a rescaled ten-fold convolution seed with transform
L(s) = L_smoothSeed(0.5*s)^10.  The owner is still the formal closed-ball
owner under-approximated by known zeta zeros, the hypothetical orbit, and the
healthy targets.  Every n uses the same owner, same base/correction, and the
same vertex lambda = b/C.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as owner_probe  # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402


RHO = complex(0.55, 14.134725141734693)
N = 4
SEED_SCALE = 0.5
SEED_POWER = 10


def make_powered_seed(order: int = 300):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    x = 2.0 * nodes
    w = 2.0 * weights * owner_probe.smooth_seed_raw(x)

    def transform(s):
        values = np.asarray(s, dtype=complex)
        flat = values.reshape(-1)
        out = np.empty_like(flat)
        for start in range(0, flat.size, 600):
            block = flat[start:start + 600]
            out[start:start + 600] = np.sum(
                np.exp((SEED_SCALE * block)[:, None] * x[None, :]) *
                w[None, :], axis=1
            ) ** SEED_POWER
        return out.reshape(values.shape)

    return transform


def main() -> None:
    owner, targets, radius, known = owner_probe.build_owner(RHO, N)
    values = [owner_probe.target_value(RHO, z) for z in owner]
    base_values = [1.0 + 0j] * len(targets)
    seed_transform = make_powered_seed()
    seed0 = complex(seed_transform(np.array([0j]))[0])

    xi = np.arange(-25.0, 25.0001, 0.05)
    axis = 0.5 - 2j * math.pi * xi
    base_laplace = owner_probe.cardinal_transform(
        targets, base_values, seed0, axis, seed_transform)
    correction_laplace = owner_probe.cardinal_transform(
        owner, values, seed0, axis, seed_transform)
    centered_orbit = [z - 0.5 for z in targets[:4]]
    polynomial = np.real(legacy.P_from_nodes(xi, centered_orbit))

    heights = np.linspace(0.0, 160.0, 321)
    base_c4 = 0.0
    correction_c2 = 0.0
    base_c2 = 0.0
    for sigma in (0.0, 0.5, 1.0):
        s = sigma + 1j * heights
        base = owner_probe.cardinal_transform(
            targets, base_values, seed0, s, seed_transform)
        correction = owner_probe.cardinal_transform(
            owner, values, seed0, s, seed_transform)
        scaled = np.abs(heights / (2.0 * math.pi))
        base_c4 = max(base_c4, float(np.max(scaled ** 4 * np.abs(base))))
        base_c2 = max(base_c2, float(np.max(scaled ** 2 * np.abs(base))))
        correction_c2 = max(
            correction_c2, float(np.max(scaled ** 2 * np.abs(correction))))

    H = 3.0 + abs(RHO)
    rows = []
    for n in range(5):
        support_radius = 2.0 * (n + 2)
        kernel = legacy.rig.sigma_vec(2.0 * math.pi * xi)
        prime_powers = legacy.rig.prime_powers_up_to(math.exp(support_radius))
        for integer, von_mangoldt in prime_powers:
            kernel += (2.0 * von_mangoldt / math.sqrt(integer) *
                       np.cos(2.0 * math.pi * xi * math.log(integer)))
        density = (np.abs(base_laplace) ** (2 * (n + 1)) *
                   np.abs(correction_laplace) ** 2)
        C = float(np.trapezoid(kernel * density, xi))
        b = float(np.trapezoid(kernel * polynomial * density, xi))
        D = float(np.trapezoid(kernel * polynomial * polynomial * density, xi))
        determinant = C * D - b * b
        lam = b / C if C != 0 else float("nan")
        L = (H ** 4 * (H ** 4 + abs(lam)) ** 2 * (2.0 * math.pi) ** 12 *
             ((0.5 ** n) * base_c4 * correction_c2) ** 2)
        ratio = L / (lam * lam) if lam != 0 else float("inf")
        rows.append({
            "n": n,
            "support_radius": support_radius,
            "prime_power_count": len(prime_powers),
            "C": C,
            "b": b,
            "D": D,
            "det": determinant,
            "lambda": lam,
            "tail_proxy_L_over_lambda_sq": ratio,
            "gate_signs": C > 0.0 and b > 0.0 and determinant < 0.0,
            "same_index_tail_below_one": ratio < 1.0,
        })

    report = {
        "record": 1981,
        "status": "SIGN_ONLY_TAIL_FAIL",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "owner_model": "known zeta zeros in formal closed ball + hypothetical orbit + healthy targets",
        "radius": radius,
        "known_zero_count": len(known),
        "owner_cardinality": len(owner),
        "target_cardinality": len(targets),
        "min_separation": owner_probe.min_separation(owner),
        "seed": {
            "scale": SEED_SCALE,
            "power": SEED_POWER,
            "laplace_at_zero": [seed0.real, seed0.imag],
        },
        "decay_grid": {
            "base_C4": base_c4,
            "base_C2": base_c2,
            "correction_C2": correction_c2,
            "height_max": 160.0,
            "sigma_grid": [0.0, 0.5, 1.0],
        },
        "rows": rows,
        "provenance": [
            "ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean",
            "ConnesWeilRH/Dev/C1ExplicitSmoothSeed.lean",
            "known zeros supplied by mpmath.zetazero; under-approximation only",
        ],
    }
    output = ROOT / "results" / "1981_powered_seed_underapprox.json"
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
