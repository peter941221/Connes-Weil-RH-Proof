#!/usr/bin/env python3
"""Record 2123: extend the Route-B same-owner pairing through n=6.

This is a reproducible numerical reopening probe. It keeps the record-2033
owner, seed, gate, support, and q convention unchanged and tests n=5..7 on
two xi grids. It does not certify the prime channel or the formal owner.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op  # noqa: E402
import fourpoint_coupling_scan_2028 as scan  # noqa: E402
import fourpoint_diagonal_sign_1918 as rig  # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402
import fourpoint_gate_tail_pairing_2033 as pairing  # noqa: E402

OUTPUT = ROOT / "results" / "2123_route_b_n6_reopen.json"
GAMMA = 30.424876125859513
N_OWNER = 4
N_RANGE = (5, 6, 7)
DXIS = (0.02, 0.01)
XI_MAX = 25.0
Q = 2.0 ** -14
SEED_ORDER = 300


def log(message: str) -> None:
    print("[%7.1fs] %s" % (time.time() - START, message), flush=True)


def grid(dxi: float) -> np.ndarray:
    return np.arange(-XI_MAX, XI_MAX + 0.5 * dxi, dxi)


def gate_row(xi, sigma, W, P, prime):
    fs = (W, P * W, P * P * W)
    arch = [float(np.trapezoid(sigma * f, xi)) for f in fs]
    C = arch[0] + prime[0]
    b = arch[1] + prime[1]
    D = arch[2] + prime[2]
    return {"arch": arch, "C": C, "b": b, "D": D,
            "det": C * D - b * b,
            "lambda": b / C if C else float("nan")}


def tail_proxy(H, base_c4, correction_c2, n, lam):
    if lam == 0:
        return float("inf")
    return (H ** 4 * (2.0 * math.pi) ** 12 *
            (base_c4 * correction_c2) ** 2 * Q ** (2 * n) *
            (1.0 + H ** 4 / abs(lam)) ** 2)


def main() -> None:
    global START
    START = time.time()
    rho = complex(0.55, GAMMA)
    owner, targets, radius, known = op.build_owner(rho, N_OWNER)
    values = [op.target_value(rho, z) for z in owner]
    seed_transform = powered.make_powered_seed(order=SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])

    log("building decay constants")
    heights = np.linspace(0.0, 200.0, 401)
    base_c4 = base_c2 = correction_c2 = 0.0
    for sigma_value in (0.0, 0.5, 1.0):
        s = sigma_value + 1j * heights
        base = op.cardinal_transform(
            targets, [1.0 + 0j] * len(targets), seed0, s, seed_transform)
        correction = op.cardinal_transform(
            owner, values, seed0, s, seed_transform)
        scaled = np.abs(heights / (2.0 * math.pi))
        base_c4 = max(base_c4, float(np.max(scaled ** 4 * np.abs(base))))
        base_c2 = max(base_c2, float(np.max(scaled ** 2 * np.abs(base))))
        correction_c2 = max(
            correction_c2, float(np.max(scaled ** 2 * np.abs(correction))))

    rows = []
    for dxi in DXIS:
        log("grid dxi=%g" % dxi)
        xi = grid(dxi)
        sigma = rig.sigma_vec(2.0 * math.pi * xi)
        P = np.real(legacy.P_from_nodes(
            xi, [z - 0.5 for z in op.healthy_targets(rho)[:4]]))
        axis = 0.5 - 2j * math.pi * xi
        base_laplace = op.cardinal_transform(
            targets, [1.0 + 0j] * len(targets), seed0, axis, seed_transform)
        correction_laplace = op.cardinal_transform(
            owner, values, seed0, axis, seed_transform)
        for n in N_RANGE:
            cutoff = 2.0 * (n + 2)
            prime_values, prime_logs = scan.fast_prime_powers_up_to(
                math.exp(cutoff))
            prime_kernel = scan.direct_prime_channel(
                xi, prime_values, prime_logs)
            W = (np.abs(base_laplace) ** (2 * (n + 1)) *
                 np.abs(correction_laplace) ** 2)
            prime = [
                float(np.trapezoid(prime_kernel * W, xi)),
                float(np.trapezoid(prime_kernel * P * W, xi)),
                float(np.trapezoid(prime_kernel * P * P * W, xi)),
            ]
            gate = gate_row(xi, sigma, W, P, prime)
            gate.update({
                "dxi": dxi,
                "n": n,
                "prime_book": int(prime_values.size),
                "support_radius": cutoff,
                "gate_signs": bool(gate["C"] > 0 and gate["b"] > 0 and
                                    gate["det"] < 0),
                "tail_proxy": tail_proxy(
                    3.0 + abs(rho), base_c4, correction_c2, n,
                    gate["lambda"]),
            })
            gate["tail_closed"] = bool(gate["tail_proxy"] < 1.0)
            gate["joint"] = bool(gate["gate_signs"] and gate["tail_closed"])
            rows.append(gate)
            log("n=%d C=%+.6e b=%+.6e det=%+.6e gate=%s tail=%+.3e joint=%s"
                % (n, gate["C"], gate["b"], gate["det"],
                   gate["gate_signs"], gate["tail_proxy"], gate["joint"]))

    by_n = {}
    for n in N_RANGE:
        pair = [row for row in rows if row["n"] == n]
        primary = next(row for row in pair if row["dxi"] == DXIS[0])
        fine = next(row for row in pair if row["dxi"] == DXIS[1])
        drift = {}
        for key in ("C", "b", "D", "det"):
            drift[key] = (abs(fine[key] / primary[key] - 1.0)
                          if primary[key] else float("inf"))
        by_n[str(n)] = {"primary": primary, "fine": fine, "relative_drift": drift,
                        "sign_stable": bool(all(
                            (primary[key] > 0) == (fine[key] > 0)
                            for key in ("C", "b")) and
                        ((primary["det"] < 0) == (fine["det"] < 0))),
                        "joint_both_grids": bool(primary["joint"] and fine["joint"])}

    result = {
        "record": 2123,
        "status": ("GO-CANDIDATE" if any(v["joint_both_grids"]
                                         for v in by_n.values())
                    else "NO-JOINT-ROW"),
        "owner": {"rho": [rho.real, rho.imag], "N": N_OWNER,
                  "owner_cardinality": len(owner), "known_zero_count": len(known),
                  "radius": radius},
        "seed": {"scale": powered.SEED_SCALE, "power": powered.SEED_POWER,
                 "order": SEED_ORDER},
        "q": Q,
        "decay": {"base_C4": base_c4, "base_C2": base_c2,
                  "correction_C2": correction_c2},
        "rows": rows,
        "by_n": by_n,
        "nonclaims": [
            "under-approximate owner only",
            "prime channel is sampled, not interval-certified",
            "no formal producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "prior_record": "results/2033_gate_tail_pairing.json"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
