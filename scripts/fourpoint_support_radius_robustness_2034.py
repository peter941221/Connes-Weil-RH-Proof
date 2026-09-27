#!/usr/bin/env python3
"""Record 2034: support-radius robustness of the found gate rows.

Pre-registered in docs/proofs/2034_support_radius_robustness_preregistration.md.
Re-reads the record-2032 found rows with the prime cut moved to
exp(2(n+2) + delta), delta in {-1, +1, +2}.  No new gate row, no new owner.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op      # noqa: E402
import fourpoint_coupling_scan_2028 as scan   # noqa: E402
import fourpoint_diagonal_sign_1918 as rig    # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402

T0 = time.time()
DXI = 0.02
XI_MAX = 25.0
DELTAS = (-1, 1, 2)
ROUTE_CAP_B = 60000
ROWS = []
for gamma, ns in ((21.022039638771556, (0, 2)),
                  (30.424876125859513, (0, 2, 3))):
    for N in (3, 4, 5):
        for n in ns:
            ROWS.append((gamma, N, n))


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def kernel_with_cutoff(xi, cutoff_log):
    vals, logs = scan.fast_prime_powers_up_to(math.exp(cutoff_log))
    kp = scan.direct_prime_channel(xi, vals, logs)
    return kp, int(vals.size), vals, logs


def main():
    report = {
        "record": 2034,
        "status": "PENDING",
        "preregistration":
            "docs/proofs/2034_support_radius_robustness_preregistration.md",
        "deltas": list(DELTAS),
        "dxi": DXI,
        "rows_registered": [{"gamma": g, "N": N, "n": n} for g, N, n in ROWS],
    }
    xi = np.arange(-XI_MAX, XI_MAX + 0.5 * DXI, DXI)
    sig = rig.sigma_vec(2.0 * math.pi * xi)
    seed_transform = powered.make_powered_seed(order=scan.SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])

    kernels = {}
    for gamma, N, n in ROWS:
        for delta in (0,) + DELTAS:
            key = (n, delta)
            if key not in kernels:
                kernels[key] = kernel_with_cutoff(xi, 2.0 * (n + 2) + delta)

    rows = []
    fragile = []
    for gamma, N, n in ROWS:
        rho = complex(0.55, gamma)
        owner, targets, radius, known = op.build_owner(rho, N)
        values = [op.target_value(rho, z) for z in owner]
        centered_orbit = [z - 0.5 for z in op.healthy_targets(rho)[:4]]
        P = np.real(legacy.P_from_nodes(xi, centered_orbit))
        W = scan.build_density(xi, seed_transform, seed0, owner, targets,
                               values, n)
        fs = (W, P * W, P * P * W)
        entry = {"gamma": gamma, "N": N, "n": n,
                 "owner_cardinality": len(owner)}
        for delta in (0,) + DELTAS:
            kp, count, vals, logs = kernels[(n, delta)]
            meta = None
            if count <= ROUTE_CAP_B:
                route = "B"
                pr = [float(np.trapezoid(kp * f, xi)) for f in fs]
            else:
                route = "A (UNCERTIFIED)"
                pr, meta = scan.fft_prime_channel(xi, fs, vals, logs)
            arch = [float(np.trapezoid(sig * f, xi)) for f in fs]
            C = arch[0] + pr[0]
            b = arch[1] + pr[1]
            D = arch[2] + pr[2]
            det = C * D - b * b
            tag = "delta%+d" % delta
            entry[tag] = {"prime_power_count": count, "route": route,
                          "C": C, "b": b, "det": det,
                          "gate_signs": bool(C > 0 and b > 0 and det < 0),
                          "route_coverage": meta}
            log("  gamma=%7.3f N=%d n=%d %s primes=%d route=%s C=%+ .5e "
                "det=%+ .5e signs=%s" % (gamma, N, n, tag, count, route, C,
                                         det, entry[tag]["gate_signs"]))
        base_signs = entry["delta+0"]["gate_signs"]
        moved = [d for d in DELTAS
                 if entry["delta%+d" % d]["gate_signs"] != base_signs]
        entry["pattern_stable"] = bool(not moved)
        entry["moved_at"] = moved
        if base_signs and moved:
            fragile.append({"gamma": gamma, "N": N, "n": n,
                            "moved_at": [d for d in moved if d > 0]})
        rows.append(entry)
    report["rows"] = rows
    report["status"] = "RADIUS-FRAGILE" if fragile else "RADIUS-ROBUST"
    report["fragile_rows"] = fragile
    out = ROOT / "results" / "2034_support_radius_robustness.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log("wrote %s" % out)
    print(json.dumps({"status": report["status"],
                      "fragile_rows": report["fragile_rows"]}, indent=2))


if __name__ == "__main__":
    main()
