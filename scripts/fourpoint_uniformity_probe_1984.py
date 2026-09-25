#!/usr/bin/env python3
# fourpoint_uniformity_probe_1984.py — record 1984 (uniformity-layer pricing)
#
# Pre-registered (docs/proofs/1984_uniformity_pricing.md, committed BEFORE
# this run) measurement of what the uniformity layer must certify:
#   gamma-scaling  : does the scale-0.90 rescue band persist to large gamma?
#   delta-fine     : are the faces stable open blocks (no knife edges)?
#   dead-patch edge: does the rescue dominate across the whole patch?
# World model exactly record-1983; kill width pool extended to six entries
# (large gamma puts all six established ordinates inside the ball radius,
# M = 14).  No gate sign is proved; classification per the registration.

import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59    # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_offline_owner_1981 as r81     # noqa: E402

T0 = time.time()
WIDTHS_MAIN = list(r81.WIDTHS_H1)
WIDTHS_REAL = list(r81.WIDTHS_REAL)
WIDTHS_KILL = list(r81.WIDTHS_KILL) + [3.8, 4.2]


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def kill_zeros_u(rho, g_disp):
    r = r80.ball_radius(rho, 0)
    out = []
    for g in r80.GAMMAS:
        if abs(g - g_disp) < 1e-9:
            continue
        z = 0.5 + 1j * g
        if abs(z - rho) <= r and abs(z - rho) > 1e-9:
            out.append(z)
    return out, r


def owner_nodes_u(rho, g_disp):
    nodes, values = [], []

    def add(z, v):
        for t in nodes:
            if r81.same(t, z):
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
    for z in kill_zeros_u(rho, g_disp)[0]:
        add(z, 0j)
    return nodes, values


def family_for_u(nodes, scale, g_main):
    plan = {"main": 0, "real": 0, "kill": 0}
    pools = {"main": WIDTHS_MAIN, "real": WIDTHS_REAL, "kill": WIDTHS_KILL}
    fam = []
    for z in nodes:
        iz = float(np.imag(z))
        if abs(abs(iz) - g_main) < 1e-9:
            key = "main"
        elif abs(iz) < 1e-9:
            key = "real"
        else:
            key = "kill"
        idx = plan[key]
        plan[key] = idx + 1
        if idx >= len(pools[key]):
            raise RuntimeError("pool exhausted: %s" % key)
        fam.append((scale * pools[key][idx], -iz))
    return fam


def face_of(rec):
    if (rec["pin_err_base"] > 1e-6 or rec["pin_err_corr"] > 1e-6
            or rec["cond"] > 1e8 or not rec["density_finite"]):
        return "INSTRUMENT"
    if max(rec["spread_C"], rec["spread_B01"], rec["spread_D"]) > 1.0 / 3.0:
        return "UNRESOLVED_SPREAD"
    D, B, C, det = rec["D"], rec["B01"], rec["C"], rec["det"]
    disc = B * B - 4.0 * C * D
    if D < 0.0:
        return "WIRE1"
    if B > 0.0 and C > 0.0 and det < 0.0:
        return "WIRE2"
    if D < 0.0 or (D == 0.0 and B != 0.0) or (D > 0.0 and disc >= 0.0):
        return "GAP"
    return "DEAD"


def run_row(delta, gk, scale, n=0, k=30.0, xi_max=40.0, dxi=0.008):
    rho = (0.5 + delta) + 1j * gk
    tag = "d=%.2f g=%7.4f sc=%.2f n=%d" % (delta, gk, scale, n)
    log("row %s" % tag)
    nodes, values = owner_nodes_u(rho, gk)
    fam = family_for_u(nodes, scale, gk)
    XW = r80.family_quad(fam, k)
    A = r80.amplitudes(nodes, values, fam, k, XW)
    pins = r80.check_pins(nodes, values, fam, k, XW, (A[0], A[1]))
    pin_b = max(p["err_base"] for p in pins)
    pin_c = max(p["err_corr"] for p in pins)
    cond = max(A[2]["base"]["cond"], A[2]["corr"]["cond"])

    nxi = int(round(2.0 * xi_max / dxi)) + 1
    xi = np.linspace(-xi_max, xi_max, nxi)
    with np.errstate(over="ignore", invalid="ignore"):
        W, Lb, _Lc, _r = r80.owner_density(nodes, fam, k, n, xi, XW,
                                           (A[0], A[1]))
        finite = bool(np.isfinite(W).all()) and bool(np.isfinite(Lb).all())
        if finite:
            P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
            ge = r59.gate_entries(xi, W, P, max(a for a, _ in fam) * 2)
            spread = r59.route_spread(ge)
            D, C, B01 = ge["D"], ge["C"], ge["B01"]
            det = D * C - B01 * B01
        else:
            ge, spread = None, (np.inf,) * 3
            D = C = B01 = det = np.nan
    cont = r81.contraction_local(nodes, values, fam, k, XW,
                                 tmax=max(100.0, 1.5 * gk)) if finite \
        else {"T_need": None, "global_max": np.nan}
    rec = {
        "tag": tag, "delta": delta, "gamma": gk, "scale": scale, "n": n,
        "M": len(nodes), "pin_err_base": pin_b, "pin_err_corr": pin_c,
        "cond": cond, "density_finite": finite,
        "C": C, "B01": B01, "D": D, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
        "contraction_T_need": cont["T_need"],
    }
    rec["face"] = face_of(rec)
    log("  M=%d cond %.1e | C=%+.3e b=%+.3e D=%+.5e det=%+.3e -> %s"
        % (rec["M"], cond, C, B01, D, det, rec["face"]))
    return rec


def run_cell(delta, gk, scales):
    tried = []
    for sc in scales:
        r = run_row(delta, gk, sc)
        if r["face"] == "UNRESOLVED_SPREAD":
            r = run_row(delta, gk, sc, dxi=0.004)
            if r["face"] == "UNRESOLVED_SPREAD":
                r = run_row(delta, gk, sc, dxi=0.002)
        tried.append(r)
        if r["face"] in ("WIRE1", "WIRE2"):
            break
    best = next((r for r in tried
                 if r["face"] in ("WIRE1", "WIRE2")), tried[-1])
    log("CELL d=%.2f g=%.4f -> %s" % (delta, gk, best["face"]))
    return {"delta": delta, "gamma": gk, "rows": tried,
            "best_face": best["face"]}


def main():
    gam_scan = []
    for gk in (50.0, 80.0, 120.0, 200.0, 400.0):
        for delta in (0.10, 0.30):
            gam_scan.append(run_cell(delta, gk, (1.00, 0.90)))
    fine_g1 = []
    for delta in (0.02, 0.03, 0.04, 0.05, 0.06, 0.08):
        fine_g1.append(run_cell(delta, r80.GAMMA1, (1.00,)))
    dead_edge = []
    for delta in (0.22, 0.24, 0.26, 0.28, 0.30, 0.32):
        dead_edge.append(run_cell(delta, r80.GAMMAS[2], (1.00, 0.90)))
    large_d = []
    for delta in (0.40, 0.45, 0.48):
        large_d.append(run_cell(delta, r80.GAMMAS[1], (1.00,)))

    cells = gam_scan + fine_g1 + dead_edge + large_d
    faces = {}
    for c in cells:
        faces[c["best_face"]] = faces.get(c["best_face"], 0) + 1
    d090 = [abs(c["rows"][1]["D"]) for c in gam_scan
            if len(c["rows"]) > 1]
    dom_ok = all(v >= 1e6 for v in d090)
    flips = 0
    for block in (fine_g1, dead_edge):
        signs = set()
        for c in block:
            r = c["rows"][0]
            if r["face"] in ("WIRE1",):
                signs.add("neg")
            elif r["face"] in ("WIRE2", "GAP", "DEAD"):
                signs.add("pos")
        if len(signs) > 1:
            flips += 1
    if faces.get("DEAD", 0) > 0:
        verdict = "UNIFORMITY_BROKEN"
    elif not dom_ok:
        verdict = "UNIFORMITY_WEAK"
    elif flips > 0:
        verdict = "UNIFORMITY_WEAK"
    else:
        verdict = "UNIFORMITY_SUPPORTED"
    report = {
        "record": 1984,
        "status": "UNIFORMITY_PRICING_PROBE",
        "pre_registration": "docs/proofs/1984_uniformity_pricing.md",
        "verdict": verdict,
        "face_counts": faces,
        "gamma_scan_absD_scale090": d090,
        "fine_blocks_with_sign_flip": flips,
        "blocks": {"gamma_scan": gam_scan, "fine_g1": fine_g1,
                   "dead_edge": dead_edge, "large_delta": large_d},
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1984_uniformity_probe.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("VERDICT: %s ; faces %s ; flips %d" % (verdict, faces, flips))
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
