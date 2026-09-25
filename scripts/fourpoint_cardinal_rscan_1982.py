#!/usr/bin/env python3
# fourpoint_cardinal_rscan_1982.py — record 1982 (map 106, deterministic-route probe)
#
# The deterministic-construction probe.  The committed interpolation base
# cardinalRaw/explicitSeed (record 1958 formulas; seed_r(x) =
# r^{-1} smoothTransition(2 - |x|/r), support |x| < 2r) is ALREADY a Lean
# object: its interpolation pins are formal (records 1962-1963) and its L^1
# mass budget is formal on the complete healthy owner (records 1977-1978).
# Record 1959 section 1.3 measured it ONLY at r = 1 and found the density
# 99.9% beyond |xi| > 4 with the strip contraction failing on the scanned
# range — a FAILURE AT ONE KNOB, never a knob scan.  By Fourier duality the
# frequency spread scales like 1/(window width), so larger r concentrates
# the transform at low |xi|.  This rig scans r.
#
# If some r passes the three admissibility readings (mass confinement,
# strip contraction T_need, measurable gate entries with D < 0) at the
# record-1981 registered point (rho = 1/2 + 0.10 + i*gamma_1, N = 0,
# M = 12), then the deterministic route is live: the object whose gate must
# be certified IS the committed Lean object, and layer 4 of the 1981
# analysis (representative-to-construction transfer) collapses to interval
# certification on an existing definition.
#
# Readings per r (no classification this record — scouting):
#   pins (should be exact to machine level by design),
#   W(0), density peak, mass beyond |xi| > 4, 6,
#   strip contraction max |L_base| and T_need (t up to 400),
#   gate entries C, b, D with certified spreads and the 1919 identity.
#
# No gate sign is proved here; this is a scouting run for the
# deterministic-construction program.

import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59   # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_offline_owner_1981 as r81   # noqa: E402

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def cardinal_L(nodes, ys, r, s, mass0):
    """L(s) = sum_z y_z/(np z z L_seed(0)) * np z s * L_seed(s - z)
    [Dev/C1ExplicitFiniteNodeCorrection.lean:122, record-1958 formulas]."""
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    XW = r59.phi_weights(2.0 * r, panels=6, m=400)
    seed_w = r59.seed_fun(XW[0], r) * XW[1]
    total = np.zeros_like(s)
    for z, y in zip(nodes, ys):
        ls = np.exp(np.outer(s - z, XW[0])) @ seed_w
        total += (y / (r59.node_product(nodes, z, z) * mass0)) \
            * r59.node_product(nodes, z, s, vec=True) * ls
    return total


def run_r(r, delta, n=0, xi_max=40.0, dxi=0.004, tmax=400.0, nt=200):
    rho = (0.5 + delta) + 1j * r80.GAMMA1
    gamma = r80.GAMMA1
    tag = "cardinal r=%.1f d=%.2f n=%d" % (r, delta, n)
    log("case %s" % tag)
    nodes, values = r81.owner_nodes_offline(rho)
    kills, radius = r81.kill_zeros_offline(rho, 0)
    ones = np.ones(len(nodes), dtype=complex)
    XW = r59.phi_weights(2.0 * r, panels=6, m=400)
    mass0 = float(np.sum(r59.seed_fun(XW[0], r) * XW[1]))

    # pins (exact interpolation by construction; verify at machine level)
    pin_b = 0.0
    pin_c = 0.0
    for z, y in zip(nodes, values):
        Lb = complex(cardinal_L(nodes, ones, r, np.array([z]), mass0)[0])
        Lc = complex(cardinal_L(nodes, values, r, np.array([z]), mass0)[0])
        pin_b = max(pin_b, abs(Lb - 1.0))
        pin_c = max(pin_c, abs(Lc - y))

    # strip contraction of the base transform
    ts = np.linspace(0.0, tmax, nt)
    prof = np.zeros(nt)
    for s0 in (0.0, 0.25, 0.5, 0.75, 1.0):
        grid = np.asarray(s0 + 1j * ts, dtype=complex)
        prof = np.maximum(prof, np.abs(cardinal_L(nodes, ones, r, grid,
                                                  mass0)))
    T_need = None
    for i in range(nt):
        if prof[i:].max() <= 0.5:
            T_need = float(ts[i])
            break

    # density and gate entries
    nxi = int(round(2.0 * xi_max / dxi)) + 1
    xi = np.linspace(-xi_max, xi_max, nxi)
    s = 0.5 - 2j * np.pi * xi
    Lb = cardinal_L(nodes, ones, r, s, mass0)
    Lc = cardinal_L(nodes, values, r, s, mass0)
    W = np.abs(Lb) ** (2 * (n + 1)) * np.abs(Lc) ** 2
    P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
    support_radius = 2.0 * r * (n + 2)
    ge = r59.gate_entries(xi, W, P, support_radius)
    spread = r59.route_spread(ge)
    dxi_eff = float(xi[1] - xi[0])
    tot = float(np.sum(W) * dxi_eff)
    W0 = float(W[np.argmin(np.abs(xi))])
    xp = float(xi[np.argmax(W)])
    tail4 = r59.tail_fraction(xi, W, 4.0)[0]
    tail6 = r59.tail_fraction(xi, W, 6.0)[0]

    D, C, B01 = ge["D"], ge["C"], ge["B01"]
    det = D * C - B01 * B01
    vc = r59.variance_check(ge["mu"], P, xi, delta, gamma) if "mu" in ge \
        else None

    rec = {
        "tag": tag, "r": r, "delta": delta, "n": n, "M": len(nodes),
        "ball_radius": radius,
        "kill_imag": [float(z.imag) for z in kills],
        "pin_err_base": pin_b, "pin_err_corr": pin_c, "mass0": mass0,
        "W0": W0, "xi_peak": xp, "mass": tot,
        "tail_gt4": tail4, "tail_gt6": tail6,
        "support_radius": support_radius, "n_primes": ge["n_primes"],
        "arch_C": ge["arch"][0], "arch_B01": ge["arch"][1],
        "arch_D": ge["arch"][2],
        "prime_C": ge["prime"][ge["route_key"]][0],
        "prime_B01": ge["prime"][ge["route_key"]][1],
        "prime_D": ge["prime"][ge["route_key"]][2],
        "C": C, "B01": B01, "D": D, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
        "routes": sorted(ge["prime"].keys()),
        "variance_check": vc,
        "contraction_T_need": T_need,
        "contraction_max": float(prof.max()),
    }
    log("  pins: |L_base-1| %.2e ; |L_corr-y| %.2e ; mass0 %.6f"
        % (pin_b, pin_c, mass0))
    log("  W(0) = %.2e ; peak |xi| = %+.4f ; tail>4 = %.2e ; tail>6 = %.2e"
        % (W0, xp, tail4, tail6))
    log("  contraction: max|L_base| %.3e on t<=%.0f ; T_need = %s"
        % (prof.max(), tmax, str(T_need)))
    log("  full   C=%+.6e b=%+.6e D=%+.6e det=%+.6e" % (C, B01, D, det))
    log("  spread (rel): C %.1e b %.1e D %.1e  [routes %s]"
        % (spread[0], spread[1], spread[2], ",".join(rec["routes"])))
    if vc:
        d1 = abs(vc["det_var"] - det) / max(abs(det), 1e-300)
        log("  1919 identity: det_var rel %.1e" % d1)
    return rec


def main():
    quick = "--quick" in sys.argv
    xi_max, dxi = (8.0, 0.008) if quick else (40.0, 0.004)
    rs = [1.0] if quick else [1.0, 2.0, 3.0, 4.0, 6.0]
    rows = []
    for r in rs:
        rows.append(run_r(r, delta=0.10, xi_max=xi_max, dxi=dxi))
    report = {
        "record": 1982,
        "status": "DETERMINISTIC_ROUTE_SCOUT",
        "construction": "cardinalRaw/explicitSeed (record-1958 formulas), "
                        "r scan",
        "registered_point": "delta=0.10, n=0 (record-1981 GO_CANDIDATE)",
        "xi_max": xi_max, "dxi": dxi,
        "verdict": "SCOUT",
        "cases": rows,
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1982_cardinal_rscan.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
