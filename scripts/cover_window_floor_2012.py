#!/usr/bin/env python3
"""Record 2012: COVER health-window width law and delta-floor scans.

Pre-registered in docs/proofs/2012_cover_window_floor_scans_preregistration.md
(committed before this run).  Heights gamma_1..gamma_6 run through the
committed convention (record-1983 layer) and gamma_7/gamma_8 through the
height-extension layer (record-1994 EXT), with one gamma_5 EXT layer control.
The row body mirrors `fourpoint_rh_reach_probe_1983.run_row` and
`routea_opposite_gates_height_1994.run_row_ext` (same calls, same order); the
only additions are the record-1919 signed-mass readout and the omission of the
contraction scan, which this question does not use.  The copy is validated by
the K1 anchor reproduction against the committed record-1994/1996 cells.

No theorem, no Lean brick, no RH claim.
"""

import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_rh_reach_probe_1983 as r83  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402

T0 = time.time()
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COMMITTED_HEIGHTS = list(r80.GAMMAS)          # gamma_1 .. gamma_6
EXT_HEIGHTS = [r94.G7, r94.G8]                # gamma_7, gamma_8
LAYER_CONTROL = r94.G5                        # gamma_5 through the EXT layer
SCALES = [round(0.80 + 0.01 * i, 2) for i in range(21)]
WIDTH_DELTA = 0.10
FLOOR_DELTAS = (0.02, 0.05, 0.10, 0.15, 0.20, 0.30)
DXI = 0.004
K = 30.0
N = 0
XI_MAX = 40.0
PRIME_GUARD = 4000
WIDTH_STABLE_STEPS = 3
WIDTH_PINCH_STEPS = 2
WIDTH_ANCHOR_STEPS = 5
FLOOR_UNIFORM_BAR = 0.05
CHECKPOINT_EVERY = 25

# K1 anchors, committed cells of records 1994/1996 (same layer, same dxi).
ANCHORS = [
    {"layer": "ext", "gamma": r94.G7, "delta": 0.10, "scale": 0.92,
     "C": +1.732980e+02, "D": -2.035919e+20, "source": "1996"},
    {"layer": "ext", "gamma": r94.G8, "delta": 0.10, "scale": 0.88,
     "C": +6.6435e+02, "D": -1.1113e+20, "source": "1996"},
    {"layer": "committed", "gamma": r94.G5, "delta": 0.10, "scale": 0.92,
     "C": +5.788031e+01, "D": -7.618837e+09, "source": "1994"},
    {"layer": "committed", "gamma": r94.G5, "delta": 0.20, "scale": 0.86,
     "C": +8.009172e+01, "D": -2.421550e+11, "source": "1994"},
    {"layer": "ext", "gamma": r94.G5, "delta": 0.10, "scale": 0.92,
     "C": +1.494812e+00, "D": -6.307381e+12, "source": "1994b"},
]
ANCHOR_BAR = 1.0e-6


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def commit_bounds(rho, gk):
    r = r80.ball_radius(rho, 0)
    return abs((0.5 + 1j * gk) - rho), r


def measure_row(delta, gk, scale, layer):
    """One registered cell: the r83/r94 row plus the 1919 statistics."""
    rho = (0.5 + delta) + 1j * gk
    if layer == "committed":
        nodes, values = r83.owner_nodes_g(rho, gk)
        fam = r83.family_for_g(nodes, scale, gk)
        kills = r83.kill_zeros_g(rho, gk, 0)[0]
    else:
        nodes, values = r94.owner_nodes_ext(rho, gk)
        fam = r94.family_for_ext(nodes, scale, gk)
        kills = r94.kill_zeros_ext(rho, gk, 0)[0]
    XW = r80.family_quad(fam, K)
    A = r80.amplitudes(nodes, values, fam, K, XW)
    pins = r80.check_pins(nodes, values, fam, K, XW, (A[0], A[1]))
    pin_b = max(p["err_base"] for p in pins)
    pin_c = max(p["err_corr"] for p in pins)
    cond = max(A[2]["base"]["cond"], A[2]["corr"]["cond"])
    nxi = int(round(2.0 * XI_MAX / DXI)) + 1
    xi = np.linspace(-XI_MAX, XI_MAX, nxi)
    stats = None
    with np.errstate(over="ignore", invalid="ignore"):
        W, Lb, _Lc, _ratio = r80.owner_density(nodes, fam, K, N, xi, XW,
                                               (A[0], A[1]))
        finite = bool(np.isfinite(W).all()) and bool(np.isfinite(Lb).all())
        if finite:
            P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
            support_radius = max(a for a, _t in fam) * (N + 2)
            ge = r59.gate_entries(xi, W, P, support_radius)
            spread = r59.route_spread(ge)
            D, C, B01 = ge["D"], ge["C"], ge["B01"]
            det = D * C - B01 * B01
            W0 = float(W[np.argmin(np.abs(xi))])
            tail4, mass = r59.tail_fraction(xi, W, 4.0)
            try:
                mp, mm, xp, xm, vp, vm = r59.measure_stats(ge["mu"], P)
                vcheck = r59.variance_check(ge["mu"], P, xi, delta, gk)
                if vcheck is None:
                    stats = {"error": "degenerate measure (A = 0)"}
                else:
                    stats = {"mp": float(mp), "mm": float(mm),
                             "xp": float(xp), "xm": float(xm),
                             "var_plus": float(vp), "var_minus": float(vm),
                             "A": vcheck["A"], "f": vcheck["f"],
                             "sigma_p": vcheck["delta_mean"]}
            except Exception as exc:      # pragma: no cover - reported, not used
                stats = {"error": str(exc)}
            routes = sorted(ge["prime"].keys())
            n_primes = int(ge["n_primes"])
        else:
            ge, spread = None, (float("inf"),) * 3
            D = C = B01 = det = W0 = tail4 = mass = float("nan")
            routes, n_primes = [], None
    instrument_limited = bool(n_primes is not None and n_primes > PRIME_GUARD)
    certified = bool(finite and cond <= 1e8 and pin_b <= 1e-6
                     and pin_c <= 1e-6 and not instrument_limited
                     and set(r59.CERTIFIED_ROUTES) <= set(routes)
                     and spread[2] < 1.0 / 3.0)
    face = None
    if finite:
        if not certified:
            face = "INSTRUMENT" if instrument_limited else "UNRESOLVED"
        elif C > 0.0 and D < 0.0 and det < 0.0:
            face = "WIRE1"
        elif C > 0.0 and B01 > 0.0 and det < 0.0:
            face = "WIRE2"
        elif C > 0.0:
            face = "HEALTHY_NO_WIRE"
        else:
            face = "NO_HOST"
    return {
        "layer": layer, "delta": delta, "gamma": gk, "scale": scale,
        "M": len(nodes), "kill_imag": [float(z.imag) for z in kills],
        "basis_size": len(fam), "cond": cond,
        "pin_err_base": pin_b, "pin_err_corr": pin_c, "density_finite": finite,
        "C": C, "B01": B01, "D": D, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
        "W0": W0, "tail_gt4": tail4, "mass": mass,
        "n_primes": n_primes, "routes": routes, "stats": stats,
        "instrument_limited": instrument_limited, "certified": certified,
        "host": bool(certified and C > 0.0 and D < 0.0 and det < 0.0),
        "c_positive": bool(certified and C > 0.0),
        "face": face,
    }


def scan(layer, gk, deltas, scales):
    """Run the registered grid, checkpointing as it goes."""
    rows = []
    for delta in deltas:
        for scale in scales:
            row = measure_row(delta, gk, scale, layer)
            rows.append(row)
            log("  [%s g=%.4f d=%.2f sc=%.2f] np=%s C=%+.4e D=%+.4e det=%+.4e "
                "sD=%.1e face=%s" % (layer, gk, delta, scale,
                                     row["n_primes"], row["C"], row["D"],
                                     row["det"], row["spread_D"], row["face"]))
    return rows


def runs_over(cells, predicate):
    """Maximal contiguous runs of a per-scale predicate over the 21 steps."""
    out, cur = [], []
    for cell in cells:
        if predicate(cell):
            cur.append(cell["scale"])
        elif cur:
            out.append(cur)
            cur = []
    if cur:
        out.append(cur)
    return out


def main():
    smoke = "--smoke" in sys.argv
    tag = "smoke" if smoke else "full"
    log("record 2012 - COVER width law and delta-floor scans (%s)" % tag)

    if smoke:
        height_specs = [("committed", r80.GAMMA1), ("ext", r94.G7)]
        deltas = (0.10, 0.05)
        scales = (0.88, 0.92, 0.96)
    else:
        height_specs = [("committed", g) for g in COMMITTED_HEIGHTS] + \
            [("ext", g) for g in EXT_HEIGHTS] + [("ext", LAYER_CONTROL)]
        deltas = FLOOR_DELTAS
        scales = SCALES

    all_rows = {}
    for layer, gk in height_specs:
        log("scan %s gamma=%.4f" % (layer, gk))
        rows = scan(layer, gk, deltas, scales)
        all_rows[(layer, round(gk, 6))] = rows
        if not smoke:
            partial = os.path.join(REPO, "results",
                                   "2012_cover_scans_partial.json")
            with open(partial, "w", encoding="utf-8") as stream:
                json.dump({"record": "2012", "status": "PARTIAL",
                           "rows": [row for group in all_rows.values()
                                    for row in group]}, stream, indent=2)
                stream.write("\n")

    anchors = []
    for spec in ANCHORS:
        key = (spec["layer"], round(spec["gamma"], 6))
        if key not in all_rows:
            continue
        hit = [row for row in all_rows[key]
               if abs(row["delta"] - spec["delta"]) < 1e-12
               and abs(row["scale"] - spec["scale"]) < 1e-12]
        if not hit:
            continue
        row = hit[0]
        dev_c = abs(row["C"] - spec["C"]) / abs(spec["C"])
        dev_d = abs(row["D"] - spec["D"]) / abs(spec["D"])
        anchors.append({"layer": spec["layer"], "gamma": spec["gamma"],
                        "delta": spec["delta"], "scale": spec["scale"],
                        "source": spec["source"], "C": row["C"], "D": row["D"],
                        "ref_C": spec["C"], "ref_D": spec["D"],
                        "dev_C": dev_c, "dev_D": dev_d,
                        "pass": bool(dev_c <= ANCHOR_BAR
                                     and dev_d <= ANCHOR_BAR)})
        log("anchor %s g=%.4f sc=%.2f: dev_C=%.1e dev_D=%.1e pass=%s"
            % (spec["source"], spec["gamma"], spec["scale"], dev_c, dev_d,
               anchors[-1]["pass"]))

    width_map = {}
    for layer, gk in [("committed", g) for g in COMMITTED_HEIGHTS] + \
            [("ext", g) for g in EXT_HEIGHTS]:
        key = (layer, round(gk, 6))
        cells = [row for row in all_rows.get(key, [])
                 if abs(row["delta"] - WIDTH_DELTA) < 1e-12]
        cells.sort(key=lambda row: row["scale"])
        bands = runs_over(cells, lambda row: row["c_positive"])
        hosts = runs_over(cells, lambda row: row["host"])
        width_map["%s:%s" % (layer, ("%.6f" % gk))] = {
            "layer": layer, "gamma": gk, "n_cells": len(cells),
            "bands": bands, "n_bands": len(bands),
            "width_steps": max((len(b) for b in bands), default=0),
            "host_runs": hosts, "n_host_runs": len(hosts),
            "c_signs": [[row["scale"], round(row["C"], 10), row["certified"]]
                        for row in cells],
            "f_values": [[row["scale"],
                          (row["stats"] or {}).get("f")] for row in cells],
        }

    w7 = width_map.get("ext:%.6f" % r94.G7, {}).get("width_steps")
    w8 = width_map.get("ext:%.6f" % r94.G8, {}).get("width_steps")
    w1 = width_map.get("committed:%.6f" % r80.GAMMA1, {}).get("width_steps")
    if all(entry["width_steps"] >= WIDTH_STABLE_STEPS
           and entry["n_bands"] <= 1 for entry in width_map.values()):
        window_verdict = "WINDOW_STABLE"
    elif (w7 is not None and w8 is not None and w1 is not None
          and w7 <= WIDTH_PINCH_STEPS and w8 <= WIDTH_PINCH_STEPS
          and w1 >= WIDTH_ANCHOR_STEPS):
        window_verdict = "WINDOW_PINCHING"
    else:
        window_verdict = "KNOT_COMPLEX"

    floor_map = {}
    for layer, gk in [("committed", g) for g in COMMITTED_HEIGHTS] + \
            [("ext", g) for g in EXT_HEIGHTS]:
        key = (layer, round(gk, 6))
        rows = all_rows.get(key, [])
        by_delta = {}
        for delta in FLOOR_DELTAS:
            hit = [row for row in rows
                   if abs(row["delta"] - delta) < 1e-12 and row["host"]]
            by_delta[delta] = len(hit)
        with_host = sorted(d for d, count in by_delta.items() if count > 0)
        floor_map["%s:%s" % (layer, ("%.6f" % gk))] = {
            "layer": layer, "gamma": gk, "hosts_per_delta": by_delta,
            "deltas_with_host": with_host,
            "floor": (with_host[0] if with_host else None),
        }

    floors = {key: entry["floor"] for key, entry in floor_map.items()}
    f1 = floor_map.get("committed:%.6f" % r80.GAMMA1, {}).get("floor")
    f7 = floor_map.get("ext:%.6f" % r94.G7, {}).get("floor")
    f8 = floor_map.get("ext:%.6f" % r94.G8, {}).get("floor")
    known = [v for v in floors.values() if v is not None]
    if len(known) == len(floors) and all(v <= FLOOR_UNIFORM_BAR
                                         for v in known):
        floor_verdict = "FLOOR_UNIFORM"
    elif f1 is not None and ((f7 is not None and f7 > f1)
                             or (f8 is not None and f8 > f1)):
        floor_verdict = "FLOOR_RISING"
    else:
        floor_verdict = "FLOOR-MIXED"

    layer_control = None
    ctrl_key = ("ext", round(LAYER_CONTROL, 6))
    if ctrl_key in all_rows:
        c_ext = [row for row in all_rows[ctrl_key]
                 if abs(row["delta"] - WIDTH_DELTA) < 1e-12]
        c_ext.sort(key=lambda row: row["scale"])
        c_int = [row for row in all_rows.get(("committed",
                                              round(LAYER_CONTROL, 6)), [])
                 if abs(row["delta"] - WIDTH_DELTA) < 1e-12]
        c_int.sort(key=lambda row: row["scale"])
        layer_control = {
            "gamma": LAYER_CONTROL,
            "ext_bands": runs_over(c_ext, lambda row: row["c_positive"]),
            "committed_bands": runs_over(c_int, lambda row: row["c_positive"]),
            "ext_C": [[row["scale"], round(row["C"], 10)] for row in c_ext],
            "committed_C": [[row["scale"], round(row["C"], 10)]
                            for row in c_int],
        }

    verdict = "SMOKE" if smoke else "%s/%s" % (window_verdict, floor_verdict)
    log("=" * 96)
    for key, entry in width_map.items():
        log("  width %-28s bands=%d width=%d host_runs=%d"
            % (key, entry["n_bands"], entry["width_steps"],
               entry["n_host_runs"]))
    for key, entry in floor_map.items():
        log("  floor %-28s floor=%s hosts=%s"
            % (key, entry["floor"],
               {k: v for k, v in entry["hosts_per_delta"].items()}))
    log("layer control at gamma_5: %s" % json.dumps(layer_control))
    log("VERDICT: %s" % verdict)

    campaigns = {"committed": [g for g in COMMITTED_HEIGHTS],
                 "ext": list(EXT_HEIGHTS) + [LAYER_CONTROL]}
    rows = [row for group in all_rows.values() for row in group]
    suffix = "_smoke" if smoke else ""
    window_out = os.path.join(REPO, "results",
                              "2012_cover_window_law%s.json" % suffix)
    with open(window_out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2012", "scan": "width-law",
                   "width_delta": WIDTH_DELTA, "scales": list(scales),
                   "verdict": window_verdict,
                   "windows": width_map, "anchors": anchors,
                   "layer_control": layer_control,
                   "layer_campaigns": campaigns}, stream, indent=2)
        stream.write("\n")
    floor_out = os.path.join(REPO, "results",
                             "2012_cover_delta_floor%s.json" % suffix)
    with open(floor_out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2012", "scan": "delta-floor",
                   "deltas": list(FLOOR_DELTAS), "scales": list(scales),
                   "verdict": floor_verdict, "floors": floor_map,
                   "anchors": anchors, "layer_campaigns": campaigns},
                  stream, indent=2)
        stream.write("\n")
    rows_out = os.path.join(REPO, "results",
                            "2012_cover_scan_rows%s.json" % suffix)
    with open(rows_out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2012", "status": "FULL" if not smoke else "SMOKE",
                   "dxi": DXI, "rows": rows}, stream, indent=2)
        stream.write("\n")
    log("results -> %s | %s | %s" % (window_out, floor_out, rows_out))


if __name__ == "__main__":
    main()