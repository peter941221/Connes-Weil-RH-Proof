#!/usr/bin/env python3
"""Record 2032 P4: Route-B gate-row search over the registered owner family.

Pre-registered in docs/proofs/2032_full_block_assault_preregistration.md.

Question (record 2029 section 7, reopen condition 1): does a changed named
hypothesis restore the registered gate pattern C > 0, b > 0, det < 0 at an
admissible n >= 1?

Changed axes registered here
  gamma_1..gamma_3 = 14.1347..., 21.0220..., 30.4248...   (rho = 0.55 + i gamma)
  N               = 3, 4, 5                                (owner cardinality)

Held fixed (the construction's own convention, not a probe knob)
  seed            = record-1981 powered seed, scale 0.5, power 10
  support radius  = 2 (n + 2)                              (rig convention)
  prime book      = {k prime power : k <= exp(support radius)}

Every reading is an UNDERAPPROXIMATION reading on the record-1980 owner model.
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

import fourpoint_actual_owner_1980 as op      # noqa: E402
import fourpoint_coupling_scan_2028 as scan   # noqa: E402
import fourpoint_diagonal_sign_1918 as rig    # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402

T0 = time.time()

GAMMAS = (14.134725141734693, 21.022039638771556, 30.424876125859513)
N_LIST = (3, 4, 5)
N_RANGE = (0, 1, 2, 3, 4)
DXI_PRIMARY = 0.02
DXI_FINE = 0.01
XI_MAX = 25.0
CUTOFF_DELTAS = (1, 2)          # cutoff-robustness block, gamma_1 / N = 4
ROUTE_CAPS = {"Ap": 4000, "B": 60000, "A": 3000000}
CERTIFIED_ROUTES = ("Ap", "B")
ANCHOR_TOL = 1e-9
SIGN_TOL = 1e-3
SEED_ORDER = 300
SMOKE = bool(os.environ.get("RH_GATE_SEARCH_SMOKE"))


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def grid_of(dxi):
    return np.arange(-XI_MAX, XI_MAX + 0.5 * dxi, dxi)


def cut_count(cutoff_log):
    vals, logs = scan.fast_prime_powers_up_to(math.exp(cutoff_log))
    return vals, logs


def routes_for(count):
    return [name for name in ("Ap", "B", "A") if count <= ROUTE_CAPS[name]]


def prime_kernel(xi, cutoff_log):
    vals, logs = cut_count(cutoff_log)
    return scan.direct_prime_channel(xi, vals, logs), int(vals.size), vals, logs


def kernel_of(cache, cutoff_log, grid_map):
    if cutoff_log not in cache:
        out = {}
        count = 0
        for dxi, xi in grid_map.items():
            kp, count, _, _ = prime_kernel(xi, cutoff_log)
            out[dxi] = kp
        cache[cutoff_log] = (out, count)
    return cache[cutoff_log]


def orbit_P(xi, rho):
    centered_orbit = [z - 0.5 for z in op.healthy_targets(rho)[:4]]
    return np.real(legacy.P_from_nodes(xi, centered_orbit))


def gate_row(xi, sig, W, P, route_prime):
    fs = (W, P * W, P * P * W)
    arch = [float(np.trapezoid(sig * f, xi)) for f in fs]
    C = arch[0] + route_prime[0]
    b = arch[1] + route_prime[1]
    D = arch[2] + route_prime[2]
    return {"arch": arch, "C": C, "b": b, "D": D, "det": C * D - b * b,
            "lambda": (b / C) if C else float("nan")}


def main():
    report = {
        "record": 2032,
        "phase": "P4 gate-row search",
        "status": "PENDING",
        "preregistration":
            "docs/proofs/2032_full_block_assault_preregistration.md",
        "owner_model": ("known zeta zeros in formal closed ball + hypothetical "
                        "orbit + healthy targets (UNDERAPPROXIMATION)"),
        "gammas": list(GAMMAS),
        "N_list": list(N_LIST),
        "n_range": list(N_RANGE),
        "dxi_primary": DXI_PRIMARY,
        "dxi_fine": DXI_FINE,
        "seed": {"scale": powered.SEED_SCALE, "power": powered.SEED_POWER,
                 "order": SEED_ORDER},
        "support_radius_convention": "2*(n+2)",
    }

    grids = {DXI_PRIMARY: grid_of(DXI_PRIMARY), DXI_FINE: grid_of(DXI_FINE)}
    dxis = sorted(grids) if not SMOKE else [DXI_PRIMARY]
    sig_by_grid = {d: rig.sigma_vec(2.0 * math.pi * grids[d]) for d in dxis}
    kernels = {}
    for n in N_RANGE:
        kernels[n] = kernel_of({}, 2.0 * (n + 2), grids)
    report["prime_book"] = {str(n): kernels[n][1] for n in N_RANGE}

    seed_transform = powered.make_powered_seed(order=SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])

    # ------------------------------------------------------------ anchor block
    log("anchor block: gamma_1 / N = 4 against the committed record-2028 rows")
    committed = json.loads(
        (ROOT / "results" / "2028_coupling_scan.json").read_text())
    anchor_rho = complex(0.55, GAMMAS[0])
    owner_a, targets_a, _, _ = op.build_owner(anchor_rho, 4)
    values_a = [op.target_value(anchor_rho, z) for z in owner_a]
    anchor = []
    for dxi in dxis:
        xi = grids[dxi]
        P = orbit_P(xi, anchor_rho)
        for n in N_RANGE:
            W = scan.build_density(xi, seed_transform, seed0, owner_a,
                                   targets_a, values_a, n)
            kp = kernels[n][0][dxi]
            fs = (W, P * W, P * P * W)
            pr = [float(np.trapezoid(kp * f, xi)) for f in fs]
            gate = gate_row(xi, sig_by_grid[dxi], W, P, pr)
            ref = next((it for it in committed["trend"] if it["n"] == n), None)
            entry = {"dxi": dxi, "n": n, "C": gate["C"], "b": gate["b"],
                     "D": gate["D"], "det": gate["det"]}
            if ref is not None:
                entry["dev_C_vs_2028"] = abs(gate["C"] / ref["C"] - 1.0)
                entry["dev_b_vs_2028"] = abs(gate["b"] / ref["b"] - 1.0)
                entry["dev_D_vs_2028"] = abs(gate["D"] / ref["D"] - 1.0)
                entry["dev_det_vs_2028"] = abs(gate["det"] / ref["det"] - 1.0)
            anchor.append(entry)
            log("    dxi=%g n=%d C=%.8e b=%.8e det=%.8e devC=%s" % (
                dxi, n, gate["C"], gate["b"], gate["det"],
                ("%.2e" % entry["dev_C_vs_2028"])
                if "dev_C_vs_2028" in entry else "n/a"))
    prim = [e for e in anchor if e["dxi"] == DXI_PRIMARY
            and "dev_C_vs_2028" in e]
    fine = [e for e in anchor if e["dxi"] == DXI_FINE
            and "dev_C_vs_2028" in e]
    report["anchor"] = anchor
    report["anchor_max_dev_C"] = (max(e["dev_C_vs_2028"] for e in prim)
                                  if prim else None)
    report["anchor_max_dev_C_fine_grid"] = (
        max(e["dev_C_vs_2028"] for e in fine) if fine else None)
    report["anchor_passed"] = bool(
        prim and report["anchor_max_dev_C"] <= ANCHOR_TOL)

    if SMOKE:
        report["status"] = "SMOKE"
        print(json.dumps({"anchor_max_dev_C": report["anchor_max_dev_C"],
                          "prime_book": report["prime_book"]}, indent=2))
        return

    # ------------------------------------------------------------ family block
    log("family block: gamma x N x n")
    rows = []
    for gamma in GAMMAS:
        rho = complex(0.55, gamma)
        for N in N_LIST:
            owner, targets, radius, known = op.build_owner(rho, N)
            values = [op.target_value(rho, z) for z in owner]
            for n in N_RANGE:
                entry = {"gamma": gamma, "N": N, "n": n,
                         "owner_cardinality": len(owner),
                         "known_zero_count": len(known),
                         "radius": radius,
                         "min_separation": op.min_separation(owner)}
                for dxi in dxis:
                    xi = grids[dxi]
                    P = orbit_P(xi, rho)
                    W = scan.build_density(xi, seed_transform, seed0, owner,
                                           targets, values, n)
                    kp = kernels[n][0][dxi]
                    fs = (W, P * W, P * P * W)
                    pr = [float(np.trapezoid(kp * f, xi)) for f in fs]
                    gate = gate_row(xi, sig_by_grid[dxi], W, P, pr)
                    tag = "dxi%g" % dxi
                    entry[tag] = gate
                    if dxi == DXI_PRIMARY:
                        entry["pmax_xi"] = float(xi[int(np.argmax(W))])
                        entry["K_at_pmax"] = float(kp[int(np.argmax(W))])
                        entry["prime_share_C"] = (pr[0] / gate["C"]
                                                  if gate["C"] else None)
                pc = entry["dxi%g" % DXI_PRIMARY]
                fc = entry["dxi%g" % DXI_FINE]
                entry["dev_C"] = abs(fc["C"] / pc["C"] - 1.0) if pc["C"] else None
                entry["sign_stable"] = bool(
                    (pc["C"] > 0) == (fc["C"] > 0)
                    and (pc["b"] > 0) == (fc["b"] > 0)
                    and (pc["det"] < 0) == (fc["det"] < 0))
                entry["gate_signs"] = bool(pc["C"] > 0 and pc["b"] > 0
                                           and pc["det"] < 0)
                entry["certified"] = bool(
                    entry["sign_stable"] and entry["dev_C"] is not None
                    and entry["dev_C"] <= SIGN_TOL)
                rows.append(entry)
                log("  gamma=%8.4f N=%d n=%d C=%+ .6e det=%+ .6e "
                    "signs=%s stable=%s" % (
                        gamma, N, n, pc["C"], pc["det"], entry["gate_signs"],
                        entry["sign_stable"]))
    report["rows"] = rows

    found = [r for r in rows if r["n"] >= 1 and r["gate_signs"] and r["certified"]]
    healed_only_n0 = [r for r in rows if r["n"] == 0 and r["gate_signs"]]
    report["rows_found"] = [{"gamma": r["gamma"], "N": r["N"], "n": r["n"]}
                            for r in found]
    report["n0_control_rows"] = [{"gamma": r["gamma"], "N": r["N"]}
                                 for r in healed_only_n0]
    if found:
        report["status"] = "ROW-FOUND"
    else:
        report["status"] = "NO-ROW-ON-FAMILY"

    # ---------------------------------------------------------- cutoff block
    log("cutoff-robustness block: gamma_1 / N = 4, cut exp(s_n + delta)")
    cut_rows = []
    for n in N_RANGE:
        base = next(r for r in rows if r["gamma"] == GAMMAS[0] and r["N"] == 4
                    and r["n"] == n)
        entry = {"n": n, "cutoff_delta_0": {
            "prime_power_count": kernels[n][1],
            "C": base["dxi%g" % DXI_PRIMARY]["C"],
            "det": base["dxi%g" % DXI_PRIMARY]["det"]}}
        for delta in CUTOFF_DELTAS:
            kp, count, vals, logs = prime_kernel(grids[DXI_PRIMARY],
                                                 2.0 * (n + 2) + delta)
            xi = grids[DXI_PRIMARY]
            P = orbit_P(xi, complex(0.55, GAMMAS[0]))
            W = scan.build_density(xi, seed_transform, seed0, owner_a,
                                   targets_a, values_a, n)
            fs = (W, P * W, P * P * W)
            avail = routes_for(count)
            if "B" in avail:
                pr = [float(np.trapezoid(kp * f, xi)) for f in fs]
                route = "B"
            else:
                pr, meta = scan.fft_prime_channel(xi, fs, vals, logs)
                route = "A (UNCERTIFIED)"
            gate = gate_row(xi, sig_by_grid[DXI_PRIMARY], W, P, pr)
            entry["cutoff_delta_%d" % delta] = {
                "prime_power_count": count, "route": route,
                "C": gate["C"], "det": gate["det"],
                "route_coverage": meta if route != "B" else None}
            log("  n=%d delta=%d primes=%d route=%s C=%+ .6e" % (
                n, delta, count, route, gate["C"]))
        signs = [entry["cutoff_delta_%d" % d]["C"] > 0
                 for d in (0,) + CUTOFF_DELTAS]
        entry["C_sign_stable"] = bool(len(set(signs)) == 1)
        cut_rows.append(entry)
    report["cutoff_robustness"] = cut_rows
    report["cutoff_stable"] = all(r["C_sign_stable"] for r in cut_rows)
    report["cutoff_label"] = ("CUTOFF-STABLE" if report["cutoff_stable"]
                              else "CUTOFF-SENSITIVE")

    out = ROOT / "results" / "2032_gate_row_search.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log("wrote %s" % out)
    print(json.dumps({k: report[k] for k in
                      ("status", "anchor_max_dev_C", "anchor_passed",
                       "rows_found", "n0_control_rows", "cutoff_label")},
                     indent=2))


if __name__ == "__main__":
    main()
