#!/usr/bin/env python3
# fourpoint_rh_reach_probe_1983.py — record 1983 (map 106, RH-reachability probe)
#
# Pre-registered (docs/proofs/1983_rh_reachability_probe.md, committed
# BEFORE this run) measurement of the one unpriced layer between the
# lane's deterministic construction and RH: COVERAGE of the hypothetical
# off-line plane by provable faces.
#
#   WIRE1 : D < 0                          (1981 diag-only wire)
#   WIRE2 : B > 0 and C > 0 and det < 0    (1918 det wire)
#   GAP   : witness exists (1917 trichotomy), neither wire covers it
#   DEAD  : no witness at any positive lambda -- lane-level obstruction
#
# Cell space: delta in {0.02,0.05,0.10,0.20,0.30,0.45} x displaced
# ordinate in GAMMAS (the hypothetical world displaces the k-th on-line
# zero to rho = 1/2+delta+i*gamma_k; prefix = remaining on-line
# ordinates inside the ball radius).  Knobs: primary (sc 1.00, n 0),
# rescue in order (0.90,0), (1.10,0), (1.00,1).  Instrument health gate
# BEFORE face calls; two refine tiers on spread-limited rows.  Probe C
# (vertical-decay feasibility) at the registered point.
#
# No gate sign is proved here; the verdict is mechanical per the
# pre-registration.

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
DELTAS = [0.02, 0.05, 0.10, 0.20, 0.30, 0.45]
PRIMARY = (1.0, 0)
RESCUES = [(0.9, 0), (1.1, 0), (1.0, 1)]
SPREAD_BAR = 1.0 / 3.0
FACE_RANK = {"WIRE1": 3, "WIRE2": 2, "GAP": 1, "DEAD": 0}


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ------------------------------------------------- generalized node layer

def kill_zeros_g(rho, g_disp, n_shell=0):
    """Hypothetical world: the on-line ordinate g_disp is displaced to
    rho; prefix = remaining on-line ordinates inside the ball radius.
    Generalizes r81.kill_zeros_offline (which hardcodes g_disp = GAMMA1)."""
    r = r80.ball_radius(rho, n_shell)
    out = []
    for g in r80.GAMMAS:
        if abs(g - g_disp) < 1e-9:
            continue
        z = 0.5 + 1j * g
        if abs(z - rho) <= r and abs(z - rho) > 1e-9:
            out.append(z)
    return out, r


def owner_nodes_g(rho, g_disp):
    """healthyCorrectionNodes rho 0 empty, orbit priority, kill set of the
    displaced world.  Identical to r81.owner_nodes_offline at g_disp=G1."""
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
    for z in kill_zeros_g(rho, g_disp, 0)[0]:
        add(z, 0j)
    return nodes, values


def family_for_g(nodes, scale, g_main):
    """(a_j, theta_j) per node; width pools exactly r81's, with the main
    height group keyed on the DISPLACED ordinate instead of GAMMA1.  At
    g_main = GAMMA1 this reproduces r81.family_for node for node."""
    plan = {"main": 0, "real": 0, "kill": 0}
    # kill pool extended by 3.8 for the 5-kill-radius worlds (prereg 1982 s.2)
    pools = {"main": list(r81.WIDTHS_H1), "real": list(r81.WIDTHS_REAL),
             "kill": list(r81.WIDTHS_KILL) + [3.8]}
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
        pool = pools[key]
        if idx >= len(pool):
            raise RuntimeError("width pool exhausted for group %s" % key)
        fam.append((scale * pool[idx], -iz))
    return fam


# ------------------------------------------------------------ face calls

def face_of(rec):
    """Pre-registered classification of ONE row (instrument health gate
    first).  WIRE1/WIRE2/GAP/DEAD per record 1983 section 1."""
    if (rec["pin_err_base"] > 1e-6 or rec["pin_err_corr"] > 1e-6
            or rec["cond"] > 1e8 or not rec["density_finite"]):
        return "INSTRUMENT"
    if max(rec["spread_C"], rec["spread_B01"], rec["spread_D"]) > SPREAD_BAR:
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


def run_row(delta, gk, scale, n, k=30.0, xi_max=40.0, dxi=0.008):
    rho = (0.5 + delta) + 1j * gk
    tag = "d=%.2f g=%7.4f sc=%.2f n=%d dxi=%.4f" % (delta, gk, scale, n, dxi)
    log("row %s" % tag)
    nodes, values = owner_nodes_g(rho, gk)
    fam = family_for_g(nodes, scale, gk)
    XW = r80.family_quad(fam, k)
    A = r80.amplitudes(nodes, values, fam, k, XW)
    pins = r80.check_pins(nodes, values, fam, k, XW, (A[0], A[1]))
    pin_b = max(p["err_base"] for p in pins)
    pin_c = max(p["err_corr"] for p in pins)
    cond = max(A[2]["base"]["cond"], A[2]["corr"]["cond"])

    nxi = int(round(2.0 * xi_max / dxi)) + 1
    xi = np.linspace(-xi_max, xi_max, nxi)
    with np.errstate(over="ignore", invalid="ignore"):
        W, Lb, _Lc, _ratio = r80.owner_density(nodes, fam, k, n, xi, XW,
                                               (A[0], A[1]))
        finite = bool(np.isfinite(W).all()) and bool(np.isfinite(Lb).all())
        if finite:
            P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
            support_radius = max(a for a, _ in fam) * (n + 2)
            ge = r59.gate_entries(xi, W, P, support_radius)
            spread = r59.route_spread(ge)
            D, C, B01 = ge["D"], ge["C"], ge["B01"]
            det = D * C - B01 * B01
            W0 = float(W[np.argmin(np.abs(xi))])
            tail4 = r59.tail_fraction(xi, W, 4.0)[0]
            mass = float(np.sum(W) * (xi[1] - xi[0]))
        else:
            ge, spread, D, C, B01, det = None, (np.inf,) * 3, np.nan, \
                np.nan, np.nan, np.nan
            W0, tail4, mass = np.nan, np.nan, np.nan
    cont = r81.contraction_local(nodes, values, fam, k, XW) if finite \
        else {"T_need": None, "global_max": np.nan}
    rec = {
        "tag": tag, "delta": delta, "gamma": gk, "scale": scale, "n": n,
        "k": k, "rho": [rho.real, rho.imag], "M": len(nodes),
        "kill_imag": [float(z.imag) for z in kill_zeros_g(rho, gk, 0)[0]],
        "pin_err_base": pin_b, "pin_err_corr": pin_c, "cond": cond,
        "max_A": A[2]["base"]["max_A"], "density_finite": finite,
        "W0": W0, "mass": mass, "tail_gt4": tail4,
        "C": C, "B01": B01, "D": D, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
        "contraction_T_need": cont["T_need"],
        "contraction_max": cont["global_max"],
        "n_primes": (ge["n_primes"] if ge else None),
        "routes": sorted(ge["prime"].keys()) if ge else None,
    }
    rec["face"] = face_of(rec)
    log("  M=%d pins %.1e/%.1e cond %.1e | C=%+.4e b=%+.4e D=%+.5e "
        "det=%+.4e | spread %.1e/%.1e/%.1e -> %s"
        % (rec["M"], pin_b, pin_c, cond, C, B01, D, det,
           spread[0], spread[1], spread[2], rec["face"]))
    return rec


# ------------------------------------------------ probe C: decay check

def decay_probe(delta=0.10, gk=None, scale=1.0, n=0, k=30.0,
                tmax=400.0, nt=401):
    """Per-window vertical decay and the certifiable envelope at the
    registered point.  FEASIBLE needs the sqrt(t)-linear regime with
    c_eff > 0 on [100, 400] AND envelope < 1/2 permanently by T <= tmax."""
    if gk is None:
        gk = r80.GAMMA1
    rho = (0.5 + delta) + 1j * gk
    log("probe C: decay at d=%.2f g=%.4f" % (delta, gk))
    nodes, values = owner_nodes_g(rho, gk)
    fam = family_for_g(nodes, scale, gk)
    XW = r80.family_quad(fam, k)
    A_base, _A_corr, info = r80.amplitudes(nodes, values, fam, k, XW)
    ts = np.linspace(0.0, tmax, nt)
    per_window = {}
    env = np.zeros(nt)
    for s0 in (0.0, 0.5, 1.0):
        grid = np.asarray(s0 + 1j * ts, dtype=complex)
        V = r80.family_values(fam, k, grid, XW)
        env = np.maximum(env, np.sum(np.abs(A_base)[:, None] * np.abs(V),
                                     axis=0))
        for j, (a, _th) in enumerate(fam):
            key = "a%.2f" % a
            cur = per_window.get(key)
            cand = np.abs(V[j, :])
            per_window[key] = cand if cur is None else np.maximum(cur, cand)

    def c_fit(prof, t1, t2):
        m = (ts >= t1) & (ts <= t2)
        y = np.log(np.maximum(prof[m], 1e-300))
        x = np.sqrt(ts[m])
        sl, ic = np.polyfit(x, y, 1)
        return float(sl), float(ic)

    fits = {}
    for key, prof in per_window.items():
        a = float(key[1:])
        # edge-saddle constant; the earlier sqrt(k*a/2) was a factor
        # sqrt(2) low (erratum, record 1983 section 7)
        c_theory = float(np.sqrt(k * a))
        w = {}
        for (t1, t2) in ((20.0, 50.0), (50.0, 100.0), (100.0, 200.0),
                         (200.0, 400.0)):
            sl, ic = c_fit(prof, t1, t2)
            w["%.0f_%.0f" % (t1, t2)] = {"c_eff": -sl, "logC": ic}
        fits[key] = {"c_theory_saddle": c_theory, "windows": w}

    T_env = None
    for i in range(nt):
        if env[i:].max() < 0.5:
            T_env = float(ts[i])
            break
    sl_env, ic_env = c_fit(env, 100.0, 400.0)
    c_env = -sl_env
    feasible = (c_env > 0.0 and T_env is not None and T_env <= tmax)
    out = {
        "delta": delta, "gamma": gk, "scale": scale, "n": n,
        "sum_abs_A": float(np.sum(np.abs(A_base))),
        "envelope_T_below_half": T_env,
        "envelope_c_eff_100_400": c_env,
        "envelope_value_at_400": float(env[-1]),
        "per_window_fits": fits,
        "verdict": "DECAY_FEASIBLE" if feasible else "DECAY_INADEQUATE",
    }
    log("  sum|A| = %.3e ; envelope < 1/2 beyond T = %s ; c_env(100,400) "
        "= %.3f ; E(400) = %.3e -> %s"
        % (out["sum_abs_A"], str(T_env), c_env, env[-1], out["verdict"]))
    return out


# ------------------------------------------------------------- drivers

def probe_cell(delta, gk, xi_max, dxi):
    """Primary knob + rescue set + refine tiers; best face wins."""
    tried = []
    order = [PRIMARY] + RESCUES
    best = None
    for (sc, n) in order:
        r = run_row(delta, gk, sc, n, xi_max=xi_max, dxi=dxi)
        if r["face"] == "UNRESOLVED_SPREAD" and dxi > 0.004:
            r = run_row(delta, gk, sc, n, xi_max=xi_max, dxi=0.004)
            if r["face"] == "UNRESOLVED_SPREAD" and dxi > 0.002:
                r = run_row(delta, gk, sc, n, xi_max=xi_max, dxi=0.002)
        tried.append(r)
        rank = FACE_RANK.get(r["face"])
        if rank is None:
            continue
        if best is None or rank > FACE_RANK[best["face"]]:
            best = r
        if rank >= 2:
            break
    cell = {
        "delta": delta, "gamma": gk,
        "primary_face": tried[0]["face"],
        "knobs_tried": [r["tag"] for r in tried],
        "best_face": best["face"] if best else tried[0]["face"],
        "best_row": best if best else tried[0],
        "rows": tried,
    }
    log("CELL d=%.2f g=%.4f : primary %s -> best %s"
        % (delta, gk, cell["primary_face"], cell["best_face"]))
    return cell


def selfcheck():
    """The generalized layer must reproduce r81 exactly at g_disp = G1."""
    rho = 0.6 + 1j * r80.GAMMA1
    n1, v1 = r81.owner_nodes_offline(rho)
    n2, v2 = owner_nodes_g(rho, r80.GAMMA1)
    assert len(n1) == len(n2) and all(r81.same(a, b)
                                      for a, b in zip(n1, n2)), "nodes"
    assert all(abs(a - b) < 1e-12 for a, b in zip(v1, v2)), "values"
    f1 = r81.family_for(n1, 1.0)
    f2 = family_for_g(n2, 1.0, r80.GAMMA1)
    assert all(abs(a[0] - b[0]) < 1e-12 and abs(a[1] - b[1]) < 1e-12
               for a, b in zip(f1, f2)), "family"
    k1, _ = r81.kill_zeros_offline(rho, 0)
    k2, _ = kill_zeros_g(rho, r80.GAMMA1, 0)
    assert len(k1) == len(k2) and all(r81.same(a, b)
                                      for a, b in zip(k1, k2)), "kills"
    log("selfcheck vs r81 (g_disp = gamma_1): nodes/family/kills identical")


def main():
    quick = "--quick" in sys.argv
    selfcheck()
    gammas = [r80.GAMMA1, r80.GAMMAS[2]] if quick else list(r80.GAMMAS)
    deltas = [0.10] if quick else DELTAS
    cells = []
    for gk in gammas:
        for delta in deltas:
            cells.append(probe_cell(delta, gk, 40.0, 0.008))
    counts = {}
    for c in cells:
        counts[c["best_face"]] = counts.get(c["best_face"], 0) + 1
    n_inst = counts.get("INSTRUMENT", 0)
    n_dead = counts.get("DEAD", 0)
    n_gap = counts.get("GAP", 0)
    if quick:
        verdict = "QUICK_SMOKE"
    elif n_inst > 6:
        verdict = "INSTRUMENT_BOUND"
    elif n_dead > 0:
        verdict = "OBSTRUCTED_TO_RH"
    elif n_gap > 0:
        verdict = "GAP_TO_RH"
    else:
        verdict = "COVERED_SURFACE"

    # replication anchors vs record 1981 (dxi differs: 0.008 vs 0.004)
    anchors = []
    for c in cells:
        if c["gamma"] == r80.GAMMA1 and c["delta"] in (0.05, 0.10):
            row = [r for r in c["rows"] if r["scale"] == 1.0
                   and r["n"] == 0][0]
            ref = 1.0057e+06 if c["delta"] == 0.05 else -1.0737e+06
            rel = abs(row["D"] - ref) / abs(ref)
            anchors.append({"delta": c["delta"], "D_survey": row["D"],
                            "D_1981": ref, "rel_diff": rel})
    drift = max(a["rel_diff"] for a in anchors) if anchors else None
    if drift is not None and drift > 0.05 and not quick:
        log("ANCHOR DRIFT %.1e > 5e-2 -- survey void per preregistration"
            % drift)
        verdict = "INSTRUMENT_DRIFT"

    decay = None if quick else decay_probe()

    report = {
        "record": 1983,
        "status": "RH_REACHABILITY_PROBE",
        "pre_registration": "docs/proofs/1983_rh_reachability_probe.md",
        "verdict": verdict,
        "face_counts": counts,
        "instrument_cells": n_inst,
        "replication_anchors": anchors,
        "anchor_max_rel_drift": drift,
        "decay_probe": decay,
        "probeB_column_delta010": [
            {"gamma": c["gamma"], "primary_face": c["primary_face"],
             "best_face": c["best_face"], "D": c["best_row"]["D"],
             "spread_D": c["best_row"]["spread_D"]}
            for c in cells if c["delta"] == 0.10],
        "cells": [{kk: cc[kk] for kk in
                   ("delta", "gamma", "primary_face", "best_face",
                    "knobs_tried")} for cc in cells],
        "rows": [r for cc in cells for r in cc["rows"]],
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1983_rh_reach_probe.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("VERDICT: %s ; faces %s" % (verdict, counts))
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
