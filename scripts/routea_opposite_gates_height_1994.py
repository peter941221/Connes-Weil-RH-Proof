#!/usr/bin/env python3
# routea_opposite_gates_height_1994.py — record 1994 (map 104 / route
# topology 004_common_bottleneck_audit recommendation 2)
#
# PRE-REGISTERED opposite-gates height audit (docs/proofs/
# 1994_opposite_gates_height_preregistration.md, commit e60c2ed1, landed
# before this run).
#
# Route A's live assembly is the 1902 two-span opposite-gates certificate
# (ICgate(u) <= 0 < ICgate(v)); on the committed four-point owner class the
# u-side diagonal is D = ICgate(u^2) and the v-side pivot is C = ICgate(g^2).
# The committed 1983 rows read opposite gates (C > 0, D < 0) on 5/6 ordinates
# with gamma_5 the unique hole and no data beyond gamma_6.
#
# Registered cases:
#   (a) gamma_5 rescue scan — EXACTLY the 1983 convention (r83.run_row,
#       6-ordinate kill list, 13-node owner), only the scale knob moves:
#       delta in {0.10, 0.20, 0.30} x sc in {0.86, 0.88, 0.90, 0.92, 0.94};
#   (b) height extension — gamma_7, gamma_8 at delta = 0.10, sc in
#       {0.90, 1.00}, kill list extended to 10 ordinates (known-zeros
#       under-approximation), width pools extended to keep same-height rows
#       distinct (17-node owners).
#
# Verdict rules are fixed in the pre-registration.  No gate-sign theorem, no
# determinant theorem, no RH claim.

import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59   # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_rh_reach_probe_1983 as r83   # noqa: E402
import fourpoint_offline_owner_1981 as r81    # noqa: E402

T0 = time.time()

G5 = r80.GAMMAS[4]
G7 = 37.586178158825671
G8 = 40.918719012147495
# 10-ordinate kill list for the height extension (known zeros only — the
# same under-approximation class as records 1980/1981, now flagged because
# the true on-line zero set is infinite).
GAMMAS_EXT = list(r80.GAMMAS) + [G7, G8, 43.327073280914999,
                                 48.005150881167159]
KILL_POOL_EXT = list(r81.WIDTHS_KILL) + [3.8, 4.2, 4.6, 5.0, 5.4]


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ------------------------------------------------ height-extension layer

def kill_zeros_ext(rho, g_disp, n_shell=0):
    r = r80.ball_radius(rho, n_shell)
    out = []
    for g in GAMMAS_EXT:
        if abs(g - g_disp) < 1e-9:
            continue
        z = 0.5 + 1j * g
        if abs(z - rho) <= r and abs(z - rho) > 1e-9:
            out.append(z)
    return out, r


def owner_nodes_ext(rho, g_disp):
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
    for z in kill_zeros_ext(rho, g_disp, 0)[0]:
        add(z, 0j)
    return nodes, values


def family_for_ext(nodes, scale, g_main):
    plan = {"main": 0, "real": 0, "kill": 0}
    pools = {"main": list(r81.WIDTHS_H1), "real": list(r81.WIDTHS_REAL),
             "kill": list(KILL_POOL_EXT)}
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


def run_row_ext(delta, gk, scale, n, k=30.0, xi_max=40.0, dxi=0.004):
    """r83.run_row with the height-extension node/family layer."""
    rho = (0.5 + delta) + 1j * gk
    tag = "d=%.2f g=%7.4f sc=%.2f n=%d dxi=%.4f EXT" % (delta, gk, scale,
                                                        n, dxi)
    log("row %s" % tag)
    nodes, values = owner_nodes_ext(rho, gk)
    fam = family_for_ext(nodes, scale, gk)
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
            ge, spread = None, (np.inf,) * 3
            D = C = B01 = det = W0 = tail4 = mass = float("nan")
    cont = r81.contraction_local(nodes, values, fam, k, XW) if finite \
        else {"T_need": None, "global_max": float("nan")}
    rec = {
        "tag": tag, "delta": delta, "gamma": gk, "scale": scale, "n": n,
        "k": k, "rho": [rho.real, rho.imag], "M": len(nodes),
        "kill_imag": [float(z.imag) for z in kill_zeros_ext(rho, gk, 0)[0]],
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
    rec["face"] = r83.face_of(rec)
    log("  M=%d pins %.1e/%.1e cond %.1e | C=%+.4e b=%+.4e D=%+.5e "
        "det=%+.4e | spread %.1e/%.1e/%.1e -> %s"
        % (rec["M"], pin_b, pin_c, cond, C, B01, D, det,
           spread[0], spread[1], spread[2], rec["face"]))
    return rec


# ------------------------------------------------------------ verdicts

def row_ok(rec):
    """Registered opposite-gates row condition (finite, healthy, certified)."""
    if not rec["density_finite"]:
        return False
    if rec["cond"] > 1e8 or rec["pin_err_base"] > 1e-6 \
            or rec["pin_err_corr"] > 1e-6:
        return False
    return (rec["C"] > 0.0 and rec["D"] < 0.0 and rec["spread_D"] < 1.0 / 3.0)


def main():
    smoke = "--smoke" in sys.argv
    dxi = 0.008 if smoke else 0.004
    log("record 1994 — opposite-gates height audit (pre-reg e60c2ed1)")
    log("dxi=%.4f %s" % (dxi, "SMOKE" if smoke else "FULL"))

    rows = []

    # (a) gamma_5 rescue scan — 1983 convention verbatim
    g5_cases = [(0.10, 0.94)] if smoke else \
        [(d, sc) for d in (0.10, 0.20, 0.30)
         for sc in (0.86, 0.88, 0.90, 0.92, 0.94)]
    for d, sc in g5_cases:
        rows.append(r83.run_row(d, G5, sc, 0, dxi=dxi))

    # (b) height extension
    ext_cases = [(0.10, G7, 0.90)] if smoke else \
        [(0.10, G7, sc) for sc in (0.90, 1.00)] + \
        [(0.10, G8, sc) for sc in (0.90, 1.00)]
    for d, gk, sc in ext_cases:
        rows.append(run_row_ext(d, gk, sc, 0, dxi=dxi))

    g5_rows = [r for r in rows if abs(r["gamma"] - G5) < 1e-9]
    g7_rows = [r for r in rows if abs(r["gamma"] - G7) < 1e-9]
    g8_rows = [r for r in rows if abs(r["gamma"] - G8) < 1e-9]

    g5_ok = [r for r in g5_rows if row_ok(r)]
    g7_ok = [r for r in g7_rows if row_ok(r)]
    g8_ok = [r for r in g8_rows if row_ok(r)]
    det_rows = [r for r in rows if r["density_finite"]]
    det_uniform = all(r["det"] < 0.0 for r in det_rows)

    if smoke:
        verdict = "SMOKE"
    else:
        parts = []
        parts.append("G5_RESCUED" if g5_ok else "GAMMA5_HOLE_STRUCTURAL")
        parts.append("G7_HOSTS" if g7_ok else "G7_NONE")
        parts.append("G8_HOSTS" if g8_ok else "G8_NONE")
        hold = bool(g5_ok) and bool(g7_ok) and bool(g8_ok)
        verdict = "OPPOSITE_GATES_HOLD" if hold else "+".join(parts)
        if not det_uniform:
            verdict += "+DET_ANOMALY"

    log("=" * 96)
    log("gamma_5 rescue: %d/%d rows opposite-gates (of finite rows)"
        % (len(g5_ok), len([r for r in g5_rows if r["density_finite"]])))
    log("gamma_7: %d/%d ; gamma_8: %d/%d"
        % (len(g7_ok), len(g7_rows), len(g8_ok), len(g8_rows)))
    log("det < 0 on %d/%d finite rows" % (sum(1 for r in det_rows
                                              if r["det"] < 0), len(det_rows)))
    log("VERDICT: %s" % verdict)

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1994_opposite_gates_height.json")
    report = {
        "record": 1994,
        "status": "SMOKE" if smoke else "PREFLIGHT_RUN",
        "pre_registration_commit": "e60c2ed1",
        "dxi": dxi,
        "owner": "healthyCorrectionNodes displaced-ordinate convention; "
                 "gamma_5 rows = 1983 convention verbatim (r83.run_row); "
                 "gamma_7/8 rows = 10-ordinate kill extension "
                 "(under-approximation)",
        "verdict": verdict,
        "g5_opposite_rows": [r["tag"] for r in g5_ok],
        "g7_opposite_rows": [r["tag"] for r in g7_ok],
        "g8_opposite_rows": [r["tag"] for r in g8_ok],
        "det_uniform": det_uniform,
        "cases": rows,
    }
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("results -> %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
