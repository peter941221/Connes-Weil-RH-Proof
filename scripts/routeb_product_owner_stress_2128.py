#!/usr/bin/env python3
"""Record 2128: full-product owner-cardinality stress for the n=6 row.

Synthetic extra source nodes carry zero interpolation values, matching the
formal full-product indicator interface. This probes whether the product
factor, rather than one nonzero basis term per owner node, can keep the same
n=6 gate stable as owner cardinality grows. It is a stress screen only.
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
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402

OUTPUT = ROOT / "results" / "2128_routeb_product_owner_stress.json"
RHO = complex(0.55, 30.424876125859513)
N_OWNER = 4
N = 6
DXI = 0.05
XI_MAX = 25.0
SEED_ORDER = 300
COUNTS = (0, 40, 80, 160, 320)


def extra_nodes(count: int, owner: list[complex]) -> list[complex]:
    if count == 0:
        return []
    radius = op.formal_radius(RHO, N_OWNER)
    candidates = []
    for index in range(1, 20000):
        height = RHO.imag - 15.5 + 31.0 * index / 20000.0
        candidate = complex(0.5, height)
        if abs(candidate - RHO) <= radius - 1e-6 and all(
                abs(candidate - old) > 1e-7 for old in owner + candidates):
            candidates.append(candidate)
        if len(candidates) >= count:
            break
    if len(candidates) != count:
        raise RuntimeError("could not construct requested stress owner")
    return candidates


def main() -> None:
    owner0, targets, _radius, _known = op.build_owner(RHO, N_OWNER)
    seed = powered.make_powered_seed(order=SEED_ORDER)
    seed0 = complex(seed(np.array([0j]))[0])
    xi = np.arange(-XI_MAX, XI_MAX + 0.5 * DXI, DXI)
    sigma = rig.sigma_vec(2.0 * math.pi * xi)
    P = np.real(legacy.P_from_nodes(
        xi, [z - 0.5 for z in op.healthy_targets(RHO)[:4]]))
    axis = 0.5 - 2j * math.pi * xi
    base = op.cardinal_transform(
        targets, [1.0 + 0j] * len(targets), seed0, axis, seed)
    prime_values, prime_logs = scan.fast_prime_powers_up_to(math.exp(16.0))
    prime_kernel = scan.direct_prime_channel(xi, prime_values, prime_logs)
    rows = []
    for count in COUNTS:
        owner = owner0 + extra_nodes(count, owner0)
        values = [op.target_value(RHO, z) for z in owner]
        correction = op.cardinal_transform(owner, values, seed0, axis, seed)
        W = np.abs(base) ** (2 * (N + 1)) * np.abs(correction) ** 2
        fs = (W, P * W, P * P * W)
        arch = [float(np.trapezoid(sigma * f, xi)) for f in fs]
        prime = [float(np.trapezoid(prime_kernel * f, xi)) for f in fs]
        full = [arch[i] + prime[i] for i in range(3)]
        det = full[0] * full[2] - full[1] ** 2
        rows.append({
            "extra_zero_nodes": count,
            "owner_cardinality": len(owner),
            "correction_max": float(np.max(np.abs(correction))),
            "correction_finite": bool(np.isfinite(correction).all()),
            "C": full[0], "b": full[1], "D": full[2], "det": det,
            "gate_signs": bool(full[0] > 0 and full[1] > 0 and det < 0),
        })
        print(json.dumps(rows[-1]), flush=True)
    result = {
        "record": 2128,
        "status": "FULL-PRODUCT-OWNER-STRESS-SCREEN",
        "rho": [RHO.real, RHO.imag], "n": N, "dxi": DXI,
        "prime_book": int(prime_values.size), "rows": rows,
        "owner_model": "known owner plus synthetic critical-line zero nodes with zero values",
        "nonclaims": [
            "synthetic nodes are not claimed zeta zeros",
            "finite grid and direct prime channel are not interval-certified",
            "no formal-owner promotion, producer theorem, or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "source": "formal fullProductBaseFactor interface"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()