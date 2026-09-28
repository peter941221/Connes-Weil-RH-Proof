#!/usr/bin/env python3
"""Record 2125: Route-A n=6 spline-only error budget."""

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

OUTPUT = ROOT / "results" / "2125_routea_n6_spline_budget.json"
RHO = complex(0.55, 30.424876125859513)
N_OWNER = 4
N = 6
DXI = 0.02
XI_MAX = 75.0


def main() -> None:
    owner, targets, _radius, _known = op.build_owner(RHO, N_OWNER)
    values = [op.target_value(RHO, z) for z in owner]
    seed = powered.make_powered_seed(order=300)
    seed0 = complex(seed(np.array([0j]))[0])
    xi = np.arange(-XI_MAX, XI_MAX + 0.5 * DXI, DXI)
    sigma = rig.sigma_vec(2.0 * math.pi * xi)
    P = np.real(legacy.P_from_nodes(
        xi, [z - 0.5 for z in op.healthy_targets(RHO)[:4]]))
    axis = 0.5 - 2j * math.pi * xi
    base = op.cardinal_transform(
        targets, [1.0 + 0j] * len(targets), seed0, axis, seed)
    correction = op.cardinal_transform(owner, values, seed0, axis, seed)
    W = np.abs(base) ** (2 * (N + 1)) * np.abs(correction) ** 2
    fs = (W, P * W, P * P * W)
    prime_values, prime_logs = scan.fast_prime_powers_up_to(math.exp(16.0))
    route_a, coverage = scan.fft_prime_channel(
        xi, fs, prime_values, prime_logs)
    arch = [float(np.trapezoid(sigma * f, xi)) for f in fs]
    full = [arch[i] + route_a[i] for i in range(3)]
    determinant = full[0] * full[2] - full[1] ** 2
    omega_step = 1.0 / (xi[-1] - xi[0])
    weight_sum = float(np.sum(2.0 * np.asarray(prime_logs) /
                              np.sqrt(prime_values)))
    moment4 = []
    errors = []
    for f in fs:
        moment = float(np.trapezoid(np.abs(xi) ** 4 * np.abs(f), xi))
        transform_error = (omega_step ** 4 * (2.0 * math.pi) ** 4 /
                           384.0 * moment)
        moment4.append(moment)
        errors.append(weight_sum * transform_error)
    ec, eb, ed = errors
    c, b, d = full
    determinant_error = ((abs(d) * ec + abs(c) * ed + ec * ed) +
                         (2.0 * abs(b) * eb + eb ** 2))
    result = {
        "record": 2125,
        "status": "SPLINE-ONLY-ERROR-BUDGET-CANDIDATE",
        "owner": {"rho": [RHO.real, RHO.imag], "N": N_OWNER,
                  "owner_cardinality": len(owner)},
        "n": N,
        "xi": {"min": -XI_MAX, "max": XI_MAX, "dxi": DXI,
               "omega_step": omega_step},
        "prime_book": int(prime_values.size),
        "coverage": coverage,
        "prime_weight_sum": weight_sum,
        "full_route_a": {"C": c, "b": b, "D": d, "det": determinant},
        "moment4": moment4,
        "moment_error_bound": {"C": ec, "b": eb, "D": ed},
        "determinant_error_bound": determinant_error,
        "spline_margin_ratio": abs(determinant) / determinant_error,
        "nonclaims": [
            "DFT/trapezoid error not charged",
            "window tail outside |xi| <= 75 not charged",
            "owner is a known-zero under-approximation",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "source": "results/2124_route_b_n6_routea_crossread.json"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
