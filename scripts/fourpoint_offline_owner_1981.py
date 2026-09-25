#!/usr/bin/env python3
# fourpoint_offline_owner_1981.py — record 1981 (map 106, pre-registered run)
#
# The pre-registered OFFLINE-owner falsification run of docs/proofs/
# 1981_diag_obligation_audit_and_offline_preregistration.md, under the
# CORRECTED single-sign Cut-2 obligation established there:
#
#   GO_CANDIDATE : D < 0 at the registered point (window scale 1.00,
#                  convolution count n = 0) of an offline owner
#                  rho = 1/2 + delta + i*gamma_1, delta in {0.05, 0.10},
#                  with relative certified spread_D < 1/3.
#   PARK_CONFIRM : D >= 0 at BOTH offline registered points — the
#                  record-1980 freeze stands, lane back to map-043.
#
# The committed contradiction theorem requires `hoff : rho.re != 1/2`
# (C1FourPointSpectralPrefixTransport.lean:333), so the decisive owner is
# OFF-LINE; the 1980 run measured the on-line proxy. Owner: the same
# healthyCorrectionNodes rho 0 empty (M = 12 nodes when the orbit does not
# collapse: 4 orbit + rho+1/2 + real triple + 4 kill ordinates).
#
# Instrument: reuses the certified machinery of records 1959/1980
# (scripts/fourpoint_owner_density_1959.py, scripts/
# fourpoint_owner_completion_1980.py): Gauss quadrature, kernel/prime
# machinery (law F80 phase, law F81 measure weights), certified route pair,
# 1919 variance identity, contraction scan. Only the node layer is new:
# the orbit-priority target values for the non-collapsing orbit follow
# negativeSourceOrbitValue (rho -> 1, 1 - conj rho -> -1, other orbit
# points -> 0) [Source/CC20YoshidaFullProduct.lean:59-61], and the
# height-gamma_1 width pool is extended to five distinct widths for the
# five same-height nodes.
#
# No gate sign is proved here; classification is per the pre-registration.

import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59   # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# Offline width pool: five DISTINCT widths for the five nodes at
# |Im| = gamma_1 (four orbit nodes + rho + 1/2); a single width at one
# height makes the interpolation rows indistinguishable (record 1959 s.1.2).
WIDTHS_H1 = [2.0, 2.3, 2.6, 2.9, 3.2]
WIDTHS_REAL = [2.1, 2.5, 2.9]
WIDTHS_KILL = [2.2, 2.6, 3.0, 3.4]


def family_for(nodes, scale):
    g1 = r80.GAMMA1
    plan = {}
    fam = []
    for z in nodes:
        iz = float(np.imag(z))
        if abs(iz - g1) < 1e-9 or abs(iz + g1) < 1e-9:
            key, pool = "h1", WIDTHS_H1
        elif abs(iz) < 1e-9:
            key, pool = "real", WIDTHS_REAL
        else:
            key, pool = "kill", WIDTHS_KILL
        idx = plan.get(key, 0)
        plan[key] = idx + 1
        if idx >= len(pool):
            raise RuntimeError("width pool exhausted for group %s" % key)
        fam.append((scale * pool[idx], -iz))
    return fam


def kill_zeros_offline(rho, n_shell):
    """Ball-set zeros in the HYPOTHETICAL world where rho is the (offline)
    first zero: the on-line ordinate gamma_1 is displaced by rho, so the
    prefix is {rho} union {gamma_2 .. gamma_5} -- gamma_1 itself is NOT a
    node (at delta = 0 it coincides with rho and dedups; at delta > 0 it
    must not enter at all)."""
    r = r80.ball_radius(rho, n_shell)
    out = []
    for g in r80.GAMMAS:
        if abs(g - r80.GAMMA1) < 1e-9:
            continue
        z = 0.5 + 1j * g
        if abs(z - rho) <= r and abs(z - rho) > 1e-9:
            out.append(z)
    return out, r


def same(a, b):
    return abs(a - b) <= 1e-9


def contraction_local(nodes, values, fam, k, XW, tmax=100.0, nt=400,
                      sigmas=(0.0, 0.25, 0.5, 0.75, 1.0)):
    """max |L_base(sigma + i t)| on the strip grid; smallest grid T with
    tail <= 1/2 (record-1959 discipline, local node set)."""
    A_base, _, _ = r80.amplitudes(nodes, values, fam, k, XW)
    ts = np.linspace(0.0, tmax, nt)
    prof = np.zeros(nt)
    for s0 in sigmas:
        grid = np.asarray(s0 + 1j * ts, dtype=complex)
        V = r80.family_values(fam, k, grid, XW)
        prof = np.maximum(prof, np.abs(A_base @ V))
    T_need = None
    for i in range(nt):
        if prof[i:].max() <= 0.5:
            T_need = float(ts[i])
            break
    return {"T_need": T_need, "global_max": float(prof.max())}


def owner_nodes_offline(rho):
    """healthyCorrectionNodes rho 0 empty for the OFFLINE hypothetical zero:
    orbit-priority targets on the non-collapsing orbit, then rho+1/2, the
    real triple, and the ball-set zeros of the hypothetical world (the
    displaced on-line gamma_1 is NOT a node)."""
    nodes, values = [], []

    def add(z, v):
        for t in nodes:
            if same(t, z):
                return
        nodes.append(z)
        values.append(v)

    add(rho, 1.0 + 0j)
    add(1 - np.conj(rho), -1.0 + 0j)
    add(np.conj(rho), 0j)
    add(1 - rho, 0j)
    add(rho + 0.5, -1.0 + 0j)
    add(0.5 + 0j, 0j)
    add(1.0 + 0j, 0j)
    add(1.5 + 0j, 0j)
    for z in kill_zeros_offline(rho, 0)[0]:
        add(z, 0j)
    return nodes, values


def run_case(delta, scale, n, k=30.0, xi_max=40.0, dxi=0.004):
    rho = (0.5 + delta) + 1j * r80.GAMMA1
    gamma = r80.GAMMA1
    tag = "offline d=%.2f sc=%.2f k=%.1f n=%d" % (delta, scale, k, n)
    log("case %s" % tag)
    nodes, values = owner_nodes_offline(rho)
    kills, radius = kill_zeros_offline(rho, 0)
    fam = family_for(nodes, scale)
    XW = r80.family_quad(fam, k)
    A = r80.amplitudes(nodes, values, fam, k, XW)
    pins = r80.check_pins(nodes, values, fam, k, XW, (A[0], A[1]))
    pin_b = max(p["err_base"] for p in pins)
    pin_c = max(p["err_corr"] for p in pins)
    log("  M = %d nodes ; ball radius %.4f ; kill = %s"
        % (len(nodes), radius, ["%.4f" % z.imag for z in kills]))
    log("  pins: max |L_base-1| = %.2e ; max |L_corr-y| = %.2e ; cond %.2e"
        % (pin_b, pin_c, A[2]["base"]["cond"]))

    nxi = int(round(2.0 * xi_max / dxi)) + 1
    xi = np.linspace(-xi_max, xi_max, nxi)
    W, Lb, _Lc, ratio = r80.owner_density(nodes, fam, k, n, xi, XW,
                                          (A[0], A[1]))
    P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
    support_radius = max(a for a, _ in fam) * (n + 2)
    ge = r59.gate_entries(xi, W, P, support_radius)
    spread = r59.route_spread(ge)
    dxi_eff = float(xi[1] - xi[0])
    tot = float(np.sum(W) * dxi_eff)
    W0 = float(W[np.argmin(np.abs(xi))])
    xp = float(xi[np.argmax(W)])
    tail4 = r59.tail_fraction(xi, W, 4.0)[0]

    D, C, B01 = ge["D"], ge["C"], ge["B01"]
    det = D * C - B01 * B01
    # the audit-brick witness coefficient and its Cut-1 reads
    lam_w = min(1.0, abs(D) / (2.0 * (abs(B01) + abs(C) + 1.0)))
    K = 3.0 + abs(rho)
    window = (K ** 4 + lam_w) ** 2 / lam_w ** 2
    cont = contraction_local(nodes, values, fam, k, XW)
    vc = r59.variance_check(ge["mu"], P, xi, delta, gamma) if "mu" in ge \
        else None

    rec = {
        "tag": tag, "delta": delta, "scale": scale, "n": n, "k": k,
        "rho": [rho.real, rho.imag], "M": len(nodes),
        "ball_radius": radius,
        "kill_imag": [float(z.imag) for z in kills],
        "pin_err_base": pin_b, "pin_err_corr": pin_c, "solve": A[2],
        "cancel_ratio_max": float(np.max(ratio[np.abs(Lb) > 0])),
        "W0": W0, "xi_peak": xp, "mass": tot, "tail_gt4": tail4,
        "evenness_defect": r59.evenness(W, xi),
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
        "lam_witness": lam_w, "window_factor_at_witness": window,
        "contraction_T_need": cont["T_need"],
        "contraction_max": cont["global_max"],
    }
    log("  W(0) = %.2e ; peak |xi| = %+.4f ; tail>4 = %.2e"
        % (W0, xp, tail4))
    log("  full   C=%+.6e b=%+.6e D=%+.6e det=%+.6e" % (C, B01, D, det))
    log("  spread (rel): C %.1e b %.1e D %.1e  [routes %s]"
        % (spread[0], spread[1], spread[2], ",".join(rec["routes"])))
    if vc:
        d1 = abs(vc["det_var"] - det) / max(abs(det), 1e-300)
        log("  1919 identity: det_var rel %.1e" % d1)
    log("  witness lam = %.6e ; window factor %.3f ; T_need = %s"
        % (lam_w, window, str(cont["T_need"])))
    return rec


def classify(rows):
    """Pre-registered rule (commit 9a525b61): registered points are the
    (delta, sc=1.0, n=0) rows; GO if ANY of them has D < 0 with
    relative spread_D < 1/3."""
    reg = [r for r in rows if r["scale"] == 1.0 and r["n"] == 0]
    go = [r for r in reg if r["D"] < 0.0 and r["spread_D"] < 1.0 / 3.0]
    return ("GO_CANDIDATE", go) if go else ("PARK_CONFIRM", [])


def main():
    quick = "--quick" in sys.argv
    xi_max, dxi = (8.0, 0.008) if quick else (40.0, 0.004)
    knobs = [(0.05, 1.0, 0)] if quick else \
        [(0.05, 1.0, 0), (0.10, 1.0, 0),
         (0.05, 0.9, 0), (0.05, 1.1, 0), (0.05, 1.0, 1),
         (0.10, 0.9, 0), (0.10, 1.1, 0), (0.10, 1.0, 1)]
    rows = []
    for delta, scale, n in knobs:
        rows.append(run_case(delta, scale, n, xi_max=xi_max, dxi=dxi))
    verdict, go_rows = ("QUICK_SMOKE", []) if quick else classify(rows)
    report = {
        "record": 1981,
        "status": "PREFLIGHT_RUN_OFFLINE",
        "pre_registration_commit": "9a525b61",
        "owner": "healthyCorrectionNodes (1/2+delta+i*gamma_1) 0 empty",
        "obligation": "D < 0 alone (audit brick 1981); C, b unconstrained",
        "xi_max": xi_max, "dxi": dxi,
        "registered_points": ["delta=0.05 sc=1.0 n=0",
                              "delta=0.10 sc=1.0 n=0"],
        "verdict": verdict,
        "go_rows": [r["tag"] for r in go_rows],
        "cases": rows,
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1981_offline_owner.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("verdict: %s %s" % (verdict, report["go_rows"]))
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
