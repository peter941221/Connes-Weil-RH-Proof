#!/usr/bin/env python3
"""Record 2130: height scan for the Route-B n=6 Route-A candidate."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_actual_owner_1980 as op  # noqa: E402
import fourpoint_coupling_scan_2028 as scan  # noqa: E402
import fourpoint_diagonal_sign_1918 as rig  # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402
OUTPUT = ROOT / "results" / "2130_routeb_n6_height_scan.json"
GAMMAS = (30.424876125859513, 35.0, 37.586178, 40.9187190121475, 43.327073)
N_OWNER = 4
N = 6
DXI = 0.02
XI_MAX = 25.0

def main():
    xi = np.arange(-XI_MAX, XI_MAX + 0.5 * DXI, DXI)
    sigma = rig.sigma_vec(2.0 * math.pi * xi)
    seed = powered.make_powered_seed(order=300)
    prime_values, prime_logs = scan.fast_prime_powers_up_to(math.exp(16.0))
    rows = []
    for gamma in GAMMAS:
        rho = complex(0.55, gamma)
        owner, targets, radius, known = op.build_owner(rho, N_OWNER)
        values = [op.target_value(rho, z) for z in owner]
        seed0 = complex(seed(np.array([0j]))[0])
        axis = 0.5 - 2j * math.pi * xi
        base = op.cardinal_transform(targets, [1.0 + 0j] * len(targets), seed0, axis, seed)
        correction = op.cardinal_transform(owner, values, seed0, axis, seed)
        P = np.real(legacy.P_from_nodes(
            xi, [z - 0.5 for z in op.healthy_targets(rho)[:4]]))
        W = np.abs(base) ** (2 * (N + 1)) * np.abs(correction) ** 2
        fs = (W, P * W, P * P * W)
        route, meta = scan.fft_prime_channel(xi, fs, prime_values, prime_logs)
        arch = [float(np.trapezoid(sigma * f, xi)) for f in fs]
        full = [arch[i] + route[i] for i in range(3)]
        det = full[0] * full[2] - full[1] ** 2
        rows.append({
            "gamma": gamma, "owner_cardinality": len(owner),
            "known_zero_count": len(known), "radius": radius,
            "C": full[0], "b": full[1], "D": full[2], "det": det,
            "gate_signs": bool(full[0] > 0 and full[1] > 0 and det < 0),
            "coverage": meta,
        })
        print(json.dumps(rows[-1]), flush=True)
    result = {
        "record": 2130, "status": "N6-HEIGHT-SCAN-CANDIDATE",
        "n": N, "dxi": DXI, "prime_book": int(prime_values.size),
        "rows": rows,
        "nonclaims": [
            "finite height scan only", "Route-A spline/DFT not interval-certified",
            "owner is a known-zero under-approximation",
            "no continuous band, producer theorem, or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "source": "results/2123_route_b_n6_reopen.json"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
if __name__ == "__main__":
    main()