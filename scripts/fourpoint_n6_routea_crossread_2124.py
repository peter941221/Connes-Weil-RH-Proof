#!/usr/bin/env python3
"""Record 2124: direct-versus-Route-A cross-read for the n=6 row."""

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

OUTPUT = ROOT / "results" / "2124_route_b_n6_routea_crossread.json"
RHO = complex(0.55, 30.424876125859513)
N_OWNER = 4
N = 6
DXIS = (0.02, 0.01)


def main() -> None:
    owner, targets, _radius, _known = op.build_owner(RHO, N_OWNER)
    values = [op.target_value(RHO, z) for z in owner]
    seed = powered.make_powered_seed(order=300)
    seed0 = complex(seed(np.array([0j]))[0])
    rows = []
    for dxi in DXIS:
        xi = np.arange(-25.0, 25.0001, dxi)
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
        direct_kernel = scan.direct_prime_channel(
            xi, prime_values, prime_logs)
        direct = [float(np.trapezoid(direct_kernel * f, xi)) for f in fs]
        fft, meta = scan.fft_prime_channel(
            xi, fs, prime_values, prime_logs)
        arch = [float(np.trapezoid(sigma * f, xi)) for f in fs]
        full_direct = [arch[i] + direct[i] for i in range(3)]
        full_fft = [arch[i] + fft[i] for i in range(3)]
        det_direct = full_direct[0] * full_direct[2] - full_direct[1] ** 2
        det_fft = full_fft[0] * full_fft[2] - full_fft[1] ** 2
        rows.append({
            "dxi": dxi,
            "prime_book": int(prime_values.size),
            "coverage": meta,
            "arch": arch,
            "prime_direct": direct,
            "prime_route_a": [float(x) for x in fft],
            "prime_relative_drift": [
                float(abs(fft[i] / direct[i] - 1.0)) for i in range(3)],
            "full_direct": full_direct,
            "full_route_a": full_fft,
            "det_direct": det_direct,
            "det_route_a": det_fft,
            "det_relative_drift": float(abs(det_fft / det_direct - 1.0)),
            "direct_gate": bool(full_direct[0] > 0 and full_direct[1] > 0
                                and det_direct < 0),
            "route_a_gate": bool(full_fft[0] > 0 and full_fft[1] > 0
                                  and det_fft < 0),
        })
    result = {
        "record": 2124,
        "status": "ROUTE-A-COVERAGE-PASS-CROSSREAD",
        "owner": {"rho": [RHO.real, RHO.imag], "N": N_OWNER,
                  "owner_cardinality": len(owner)},
        "n": N,
        "rows": rows,
        "nonclaims": [
            "FFT/spline error is not interval-certified",
            "owner is a known-zero under-approximation",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "source": "results/2123_route_b_n6_reopen.json"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
