#!/usr/bin/env python3
"""Record 2012: COVER health-window width law and delta-floor scans.

Pre-registered in docs/proofs/2012_cover_window_floor_scans_preregistration.md
(committed before this run; the two-stage floor cost structure of its section
2a is pre-run as well).  Heights gamma_1..gamma_6 run through the committed
convention (record-1983 layer) and gamma_7/gamma_8 through the
height-extension layer (record-1994 EXT), with one gamma_5 EXT layer control.
The row body mirrors `fourpoint_rh_reach_probe_1983.run_row` and
`routea_opposite_gates_height_1994.run_row_ext` (same calls, same order); the
only additions are the record-1919 signed-mass readout and the omission of the
contraction scan, which this question does not use.  The copy is validated by
the K1 anchor reproduction against the committed record-1994/1996 cells.

No theorem, no Lean brick, no RH claim.

Record-2019 extension (pre-registered in
docs/proofs/2019_cover_resolution_refinement_preregistration.md), the two
registered COVER follow-ups of records 2016/2017/2018:

  --phase=edges    M1: re-read the complete delta = 0.10 slices of the nine
                   registered slots at dxi = 0.002, pair every cell with its
                   committed 0.004 row (preloaded through --resume-from and
                   never re-measured), and read the sign-conservation, band
                   census and eps/r tables of record 2019 sections 3-5.
  --phase=floor2   M2: the finer delta grid {0.005, 0.01} on the same slots,
                   stage A five-point positives only, with the registered
                   conditional stage-B sweep at 0.005 for every slot with no
                   stage-A host at either new delta.

From this extension the row carries its own `dxi` and the cache is keyed by
it, so one process holds the committed 0.004 rows and the fresh 0.002 rows of
the same cell without either shadowing the other.
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
ANCHOR_SCALES = (0.86, 0.88, 0.90, 0.92, 0.94)
WIDTH_DELTA = 0.10
FLOOR_DELTAS = (0.02, 0.05, 0.10, 0.15, 0.20, 0.30)
DXI = 0.004
EDGE_DXI = 0.002               # record 2019 M1: the refinement target
REFINED_DELTAS = (0.005, 0.01)  # record 2019 M2: the finer delta grid
CELLS_ARTIFACT = "results/2019_registered_cells.json"
CHECKPOINT_EVERY = 25
SMOKE_SUFFIX = ""              # set to "_smoke" by a --smoke run
K = 30.0
N = 0
XI_MAX = 40.0
PRIME_GUARD = 4000
WIDTH_STABLE_STEPS = 3
WIDTH_PINCH_STEPS = 2
WIDTH_ANCHOR_STEPS = 5
FLOOR_UNIFORM_BAR = 0.05

# K1 anchors, committed cells of records 1994/1996 (same layer, same dxi).
ANCHORS = [
    # References are the committed artifact values at full precision, not
    # prose transcriptions: record 2016 section 4 lost one anchor to a 5-digit
    # rounding grabbed from an audit paragraph.  Cell (layer, gamma, delta,
    # scale) and the artifact it is read from are both named here.
    {"layer": "ext", "gamma": r94.G7, "delta": 0.10, "scale": 0.92,
     "C": +1.73298027805540190e+02, "D": -2.03591937692186640e+20,
     "source": "1996", "artifact": "results/1996_gamma78_full_sweep.json"},
    {"layer": "ext", "gamma": r94.G8, "delta": 0.10, "scale": 0.88,
     "C": +6.64351862261741190e+02, "D": -1.11126160981345400e+20,
     "source": "1996", "artifact": "results/1996_gamma78_full_sweep.json"},
    {"layer": "committed", "gamma": r94.G5, "delta": 0.10, "scale": 0.92,
     "C": +5.78803112549221620e+01, "D": -7.61883667437500000e+09,
     "source": "1994", "artifact": "results/1994_opposite_gates_height.json"},
    {"layer": "committed", "gamma": r94.G5, "delta": 0.20, "scale": 0.86,
     "C": +8.00917241663701130e+01, "D": -2.42154963980203120e+11,
     "source": "1994", "artifact": "results/1994_opposite_gates_height.json"},
    {"layer": "ext", "gamma": r94.G5, "delta": 0.10, "scale": 0.92,
     "C": +1.49481243341233500e+00, "D": -6.30738098958158600e+12,
     "source": "1994b",
     "artifact": "results/1994b_ext_convention_control.json"},
]
ANCHOR_BAR = 1.0e-6

HEIGHTS = [("committed", g) for g in COMMITTED_HEIGHTS] + \
    [("ext", g) for g in EXT_HEIGHTS]
CONTROL = ("ext", LAYER_CONTROL)


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def measure_row(delta, gk, scale, layer, dxi=None):
    """One registered cell: the r83/r94 row plus the 1919 statistics."""
    dxi = DXI if dxi is None else dxi
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
    nxi = int(round(2.0 * XI_MAX / dxi)) + 1
    xi = np.linspace(-XI_MAX, XI_MAX, nxi)
    stats = None
    with np.errstate(over="ignore", invalid="ignore"):
        W, Lb, _Lc, _ratio = r80.owner_density(nodes, fam, K, N, xi, XW,
                                               (A[0], A[1]))
        finite = bool(np.isfinite(W).all()) and bool(np.isfinite(Lb).all())
        if finite:
            P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
            support_radius = max(a for a, _ in fam) * (N + 2)
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
            except Exception as exc:      # pragma: no cover - reported only
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
        "dxi": dxi,
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


class Cache(object):
    """Row cache keyed by (layer, gamma, delta, scale, dxi).

    The delta = 0.10 slice is shared by both 2012 scans; from the record-2019
    extension the dxi is part of the key, so one process can hold the
    committed 0.004 rows and the fresh 0.002 rows of the same cell without
    either shadowing the other.
    """

    def __init__(self):
        self.rows = {}

    @staticmethod
    def key(layer, gk, delta, scale, dxi):
        return (layer, round(gk, 6), round(delta, 6), round(scale, 6),
                round(dxi, 6))

    def get(self, layer, gk, delta, scale, dxi=None, force=False):
        dxi = DXI if dxi is None else dxi
        key = self.key(layer, gk, delta, scale, dxi)
        if force or key not in self.rows:
            row = measure_row(delta, gk, scale, layer, dxi)
            self.rows[key] = row
            log("  [%s g=%.4f d=%.2f sc=%.2f dxi=%.4f] np=%s C=%+.4e "
                "D=%+.4e det=%+.4e sD=%.1e face=%s"
                % (layer, gk, delta, scale, dxi, row["n_primes"], row["C"],
                   row["D"], row["det"], row["spread_D"], row["face"]))
        return self.rows[key]

    def peek(self, layer, gk, delta, scale, dxi=None):
        """Preloaded row or None - never measures.  The record-2019 pair
        reads take their 0.004 half from the committed artifact through this
        path, so a missing counterpart fails loudly instead of silently
        re-measuring the committed cell."""
        dxi = DXI if dxi is None else dxi
        return self.rows.get(self.key(layer, gk, delta, scale, dxi))

    def slice(self, layer, gk, delta, dxi=None):
        eff = DXI if dxi is None else dxi
        out = [row for row in self.rows.values()
               if row["layer"] == layer
               and abs(row["gamma"] - gk) < 1e-9
               and abs(row["delta"] - delta) < 1e-12
               and abs(row.get("dxi", DXI) - eff) < 1e-12]
        out.sort(key=lambda row: row["scale"])
        return out

    def dump(self, path, status="PARTIAL"):
        with open(path, "w", encoding="utf-8") as stream:
            json.dump({"record": "2012+2019", "status": status,
                       "dxi": DXI, "rows": list(self.rows.values())},
                      stream, indent=2)
            stream.write("\n")


def runs_over(cells, predicate):
    """Maximal contiguous runs of a per-scale predicate, as scale lists."""
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


def width_reading(cache, layer, gk):
    cells = cache.slice(layer, gk, WIDTH_DELTA)
    bands = runs_over(cells, lambda row: row["c_positive"])
    hosts = runs_over(cells, lambda row: row["host"])
    return {
        "layer": layer, "gamma": gk, "n_cells": len(cells),
        "bands": bands, "n_bands": len(bands),
        "width_steps": max((len(b) for b in bands), default=0),
        "host_runs": hosts, "n_host_runs": len(hosts),
        "c_signs": [[row["scale"], row["C"], row["certified"],
                     row["face"]] for row in cells],
        "f_values": [[row["scale"], (row["stats"] or {}).get("f")]
                     for row in cells],
    }


def anchor_block(cache, force=False):
    """The K1 anchor reproduction (record 2012 section 3).

    force=True re-measures the five committed anchor cells at the process dxi.
    The record-2019 phases preload their committed counterparts, so a cached
    read there would be a no-op instead of a rig-identity check; with force
    the check goes through the exact measure_row path the phase itself uses.
    """
    anchors = []
    for spec in ANCHORS:
        if not force and not any(k[0] == spec["layer"]
                                 and abs(k[1] - spec["gamma"]) < 1e-9
                                 for k in cache.rows):
            continue
        row = cache.get(spec["layer"], spec["gamma"], spec["delta"],
                        spec["scale"], force=force)
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
    return anchors


def sign_of(row):
    if not row["certified"]:
        return "u"
    return "+" if row["C"] > 0.0 else "-"


def pair_block(r4, r2):
    """The record-2019 section 3 pair quantities of one re-read cell."""
    s4, s2 = sign_of(r4), sign_of(r2)
    if s4 == "u" and s2 == "u":
        conservation = "REPORTED"          # uncertified at both resolutions
    elif s4 == "u":
        conservation = "APPEARED"          # gains a reading at the finer grid
    elif s2 == "u":
        conservation = "LOST"              # loses its reading at the finer grid
    elif s4 == s2:
        conservation = "CONSERVED"
    else:
        conservation = "FLIPPED"
    c_off = abs(r2["C"] - r4["C"]) / abs(r2["C"]) if r2["C"] else None
    d_off = abs(r2["D"] - r4["D"]) / abs(r2["D"]) if r2["D"] else None
    st4 = r4.get("stats") or {}
    st2 = r2.get("stats") or {}
    eps = None
    if all(k in st4 and k in st2 for k in ("mp", "mm")) \
            and st2["mp"] and st2["mm"]:
        eps = max(abs(st4["mp"] - st2["mp"]) / abs(st2["mp"]),
                  abs(st4["mm"] - st2["mm"]) / abs(st2["mm"]))
    f2 = st2.get("f")
    amp = abs(2.0 + f2) if f2 is not None else None
    worst = eps * amp if (eps is not None and amp is not None) else None
    ratio = (c_off / worst if (c_off is not None and worst) else None)
    return {
        "conservation": conservation, "s4": s4, "s2": s2,
        "C4": r4["C"], "C2": r2["C"], "D4": r4["D"], "D2": r2["D"],
        "c_offset": c_off, "d_offset": d_off,
        "eps": eps, "f2": f2, "amp": amp, "worst_case": worst, "r": ratio,
        "n_primes_4": r4["n_primes"], "n_primes_2": r2["n_primes"],
        "np_match": bool(r4["n_primes"] == r2["n_primes"]),
    }


def edges_reading(cache, cells_path, anchors):
    """The registered M1 reading (record 2019 sections 3-5)."""
    with open(cells_path, encoding="utf-8") as stream:
        cells = json.load(stream)
    r_keys = cells["m1"]["r_table_keys"]
    edge_set = set()
    for cell in cells["m1"]["edge_cells"]:
        edge_set.add((cell["layer"], round(cell["gamma"], 6),
                      round(cell["delta"], 6), round(cell["scale"], 6)))
    per_cell, missing = [], []
    for cell in cells["m1"]["cells"]:
        layer, gk, delta, sc = (cell["layer"], cell["gamma"], cell["delta"],
                                cell["scale"])
        r4 = cache.peek(layer, gk, delta, sc, dxi=DXI)
        r2 = cache.peek(layer, gk, delta, sc, dxi=EDGE_DXI)
        if r4 is None or r2 is None:
            missing.append({"layer": layer, "gamma": gk, "scale": sc,
                            "have_004": r4 is not None,
                            "have_002": r2 is not None})
            continue
        block = pair_block(r4, r2)
        block.update({
            "layer": layer, "gamma": gk, "delta": delta, "scale": sc,
            "is_edge": (layer, round(gk, 6), round(delta, 6),
                        round(sc, 6)) in edge_set,
            "r_table": "%s:%.6f" % (layer, gk) in r_keys,
        })
        per_cell.append(block)

    census = {}
    for key, entry in sorted(cells["m1"]["heights"].items()):
        sl = cache.slice(entry["layer"], entry["gamma"], WIDTH_DELTA,
                         dxi=EDGE_DXI)
        bands = runs_over(sl, lambda row: row["c_positive"])
        widths = [len(b) for b in bands]
        census[key] = {
            "n_bands_004": entry["n_bands"], "bands_004": entry["band_widths"],
            "n_bands_002": len(bands), "bands_002": widths,
            "reproduced": bool(len(bands) == entry["n_bands"]
                               and widths == entry["band_widths"]),
            "signs_002": "".join(sign_of(row) for row in sl),
        }

    flips = [c for c in per_cell if c["conservation"] == "FLIPPED"]
    edge_flips = [c for c in flips if c["is_edge"]]
    lost = [c for c in per_cell if c["conservation"] == "LOST"]
    appeared = [c for c in per_cell if c["conservation"] == "APPEARED"]
    np_bad = [c for c in per_cell if not c["np_match"]]
    r_rows = [c for c in per_cell if c["r_table"]]
    r_vals = sorted(c["r"] for c in r_rows if c["r"] is not None)
    r_complete = bool(r_rows) and all(c["r"] is not None for c in r_rows)
    anchor_fail = [a for a in anchors if not a["pass"]]
    instrument_fail = bool(missing or lost or np_bad or anchor_fail)
    edge_verdict = "EDGE-FLIPPED" if flips else "EDGE-CONSERVED"
    band_verdict = ("BAND-REPRODUCED"
                    if all(v["reproduced"] for v in census.values())
                    else "BAND-SHIFTED")
    if instrument_fail:
        overall = "COMB-RESOLUTION-INSTRUMENT-FAIL"
    elif edge_verdict == "EDGE-CONSERVED" and band_verdict == "BAND-REPRODUCED":
        overall = "COMB-RESOLUTION-STABLE"
    else:
        overall = "COMB-RESOLUTION-SHIFTED"

    out = os.path.join(REPO, "results",
                       "2019_band_edges_reading%s.json" % SMOKE_SUFFIX)
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({
            "record": "2019", "scan": "band-edges-d002",
            "dxi_pair": [DXI, EDGE_DXI],
            "cells_source": os.path.relpath(cells_path, REPO).replace(
                os.sep, "/"),
            "verdict": overall, "edge_verdict": edge_verdict,
            "band_verdict": band_verdict, "instrument_fail": instrument_fail,
            "n_cells": len(per_cell), "n_missing": len(missing),
            "n_flips": len(flips), "n_edge_flips": len(edge_flips),
            "n_lost": len(lost), "n_appeared": len(appeared),
            "n_np_mismatch": len(np_bad),
            "r_table_verdict": "RP-COMPLETE" if r_complete else "RP-PARTIAL",
            "r_min": r_vals[0] if r_vals else None,
            "r_max": r_vals[-1] if r_vals else None,
            "census": census, "cells": per_cell, "missing": missing,
            "anchors": anchors}, stream, indent=2)
        stream.write("\n")
    log("=" * 96)
    log("edges VERDICT: %s / %s / %s (flips %d, edge-flips %d, appeared %d, "
        "lost %d, missing %d)" % (overall, edge_verdict, band_verdict,
                                  len(flips), len(edge_flips), len(appeared),
                                  len(lost), len(missing)))
    for key, entry in sorted(census.items()):
        log("  census %-24s bands %s -> %s  widths %s -> %s  %s"
            % (key, entry["n_bands_004"], entry["n_bands_002"],
               entry["bands_004"], entry["bands_002"],
               "OK" if entry["reproduced"] else "SHIFTED"))
    log("  r table: %d cells, r in [%s, %s]"
        % (len(r_rows), r_vals[0] if r_vals else "n/a",
           r_vals[-1] if r_vals else "n/a"))
    log("results -> %s" % out)


def floor2_reading(cache, cells_path, anchors):
    """The registered M2 reading (record 2019 sections 3-5)."""
    with open(cells_path, encoding="utf-8") as stream:
        cells = json.load(stream)
    five_point = [round(p, 6) for p in cells["m2"]["five_point"]]
    with open(os.path.join(REPO, "results", "2012_cover_scan_rows_floor.json"),
              encoding="utf-8") as stream:
        committed = json.load(stream)
    ref_np = {}
    for row in committed["rows"]:
        ref_np[(row["layer"], round(row["gamma"], 6),
                round(row["scale"], 6))] = row["n_primes"]

    slot_rows, np_bad, unresolved = [], [], []
    for key in sorted(cells["m2"]["slots"]):
        entry = cells["m2"]["slots"][key]
        layer, gk = entry["layer"], entry["gamma"]
        hosts_new, swept = {}, []
        for delta in REFINED_DELTAS:
            rows_d = cache.slice(layer, gk, delta, dxi=DXI)
            hosts_new[delta] = sorted(r["scale"] for r in rows_d if r["host"])
        full_005 = cache.slice(layer, gk, REFINED_DELTAS[0], dxi=DXI)
        if not hosts_new[REFINED_DELTAS[0]] \
                and not hosts_new[REFINED_DELTAS[1]] \
                and len(full_005) > len(five_point):
            swept = [REFINED_DELTAS[0]]
            hosts_new[REFINED_DELTAS[0]] = sorted(
                r["scale"] for r in full_005 if r["host"])
        if hosts_new[REFINED_DELTAS[0]]:
            refined = REFINED_DELTAS[0]
        elif hosts_new[REFINED_DELTAS[1]]:
            refined = REFINED_DELTAS[1]
        else:
            refined = entry["committed_floor"]
        for delta in REFINED_DELTAS:
            for row in cache.slice(layer, gk, delta, dxi=DXI):
                ref = ref_np.get((layer, round(gk, 6),
                                  round(row["scale"], 6)))
                if ref is not None and ref != row["n_primes"]:
                    np_bad.append({"layer": layer, "gamma": gk,
                                   "delta": delta, "scale": row["scale"],
                                   "n_primes": row["n_primes"], "ref": ref})
                if not row["certified"]:
                    unresolved.append({"layer": layer, "gamma": gk,
                                       "delta": delta, "scale": row["scale"],
                                       "instrument_limited":
                                           row["instrument_limited"]})
        slot_rows.append({
            "layer": layer, "gamma": gk,
            "hosts_005": hosts_new[REFINED_DELTAS[0]],
            "hosts_010": hosts_new[REFINED_DELTAS[1]],
            "swept_005": swept,
            "committed_floor": entry["committed_floor"],
            "refined_floor": refined,
        })

    anchor_fail = [a for a in anchors if not a["pass"]]
    instrument_fail = bool(anchor_fail or np_bad or unresolved)
    if instrument_fail:
        overall = "FLOOR-REFINED-INSTRUMENT-FAIL"
    elif all(r["refined_floor"] == REFINED_DELTAS[0] for r in slot_rows):
        overall = "FLOOR-REFINED-0.005"
    elif all(r["refined_floor"] in REFINED_DELTAS for r in slot_rows):
        overall = "FLOOR-REFINED-0.01"
    else:
        overall = "FLOOR-REFINED-MIXED"

    out = os.path.join(REPO, "results",
                       "2019_floor_refined%s.json" % SMOKE_SUFFIX)
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({
            "record": "2019", "scan": "floor-refined",
            "deltas_new": list(REFINED_DELTAS), "dxi": DXI,
            "cells_source": os.path.relpath(cells_path, REPO).replace(
                os.sep, "/"),
            "verdict": overall, "instrument_fail": instrument_fail,
            "slots": slot_rows, "n_np_mismatch": len(np_bad),
            "unresolved": unresolved, "anchors": anchors}, stream, indent=2)
        stream.write("\n")
    log("=" * 96)
    for entry in slot_rows:
        log("  floor2 %-24s refined=%s (005 hosts %s%s, 010 hosts %s)"
            % ("%s:%.6f" % (entry["layer"], entry["gamma"]),
               entry["refined_floor"], entry["hosts_005"],
               " swept" if entry["swept_005"] else "",
               entry["hosts_010"]))
    log("VERDICT: %s" % overall)
    log("results -> %s" % out)


def verdict_only(rows_path=None):
    """Recompute the width verdict from the rows artifact.

    The verdict block is a pure function of the measured rows.  If the driver
    that wrote them aggregated the registered heights wrongly (or crashed
    after measuring), the registered verdict is recomputed here from the
    artifact instead of re-measuring 189 cells.  No threshold, no scale and no
    cell is touched.
    """
    path = rows_path or os.path.join(REPO, "results",
                                     "2012_cover_scan_rows_width.json")
    with open(path, encoding="utf-8") as stream:
        artifact = json.load(stream)
    cache = Cache()
    top_dxi = artifact.get("dxi", DXI)
    for row in artifact["rows"]:
        dxi = row.get("dxi", top_dxi)
        row.setdefault("dxi", dxi)
        cache.rows[cache.key(row["layer"], row["gamma"], row["delta"],
                             row["scale"], dxi)] = row
    log("verdict-only from %s: %d measured rows" % (path, len(artifact["rows"])))
    width_map, floor_map = {}, {}
    for layer, gk in HEIGHTS + [CONTROL]:
        if not cache.slice(layer, gk, WIDTH_DELTA):
            continue
        width_map["%s:%.6f" % (layer, gk)] = width_reading(cache, layer, gk)
    control_key = "ext:%.6f" % CONTROL[1]
    verdict_windows = {key: entry for key, entry in width_map.items()
                       if key != control_key}
    w7 = width_map.get("ext:%.6f" % r94.G7, {}).get("width_steps")
    w8 = width_map.get("ext:%.6f" % r94.G8, {}).get("width_steps")
    w1 = width_map.get("committed:%.6f" % r80.GAMMA1, {}).get("width_steps")
    if verdict_windows and all(entry["width_steps"] >= WIDTH_STABLE_STEPS
                               and entry["n_bands"] <= 1
                               for entry in verdict_windows.values()):
        window_verdict = "WINDOW_STABLE"
    elif (w7 is not None and w8 is not None and w1 is not None
          and w7 <= WIDTH_PINCH_STEPS and w8 <= WIDTH_PINCH_STEPS
          and w1 >= WIDTH_ANCHOR_STEPS):
        window_verdict = "WINDOW_PINCHING"
    else:
        window_verdict = "KNOT_COMPLEX"
    # The floor verdict belongs to the floor phase, whose own artifact carries
    # it; a width-only row set must never be read as giving a floor (a single
    # delta with a host is not a floor reading, it is the width-law slice).
    floor_map = {}
    floor_verdict = None
    log("verdict-only VERDICT: %s"
        % "/".join(part for part in (window_verdict, floor_verdict) if part))
    out = os.path.join(REPO, "results", "2012_cover_window_law.json")
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2012", "scan": "width-law",
                   "width_delta": WIDTH_DELTA, "scales": list(SCALES),
                   "verdict": window_verdict, "windows": width_map,
                   "verdict_keys": sorted(verdict_windows),
                   "control_key": control_key,
                   "layer_control_width": width_map.get(control_key),
                   "driver": {
                       "mode": "verdict-only",
                       "source": os.path.relpath(path, REPO).replace(os.sep, "/"),
                       "note": "registered width verdict recomputed from the "
                               "measured rows; the layer control is excluded "
                               "from the every-height clause per section A2"},
                   "floor_map_if_present": floor_map},
                  stream, indent=2)
        stream.write("\n")
    log("results -> %s" % out)


def main():
    global SMOKE_SUFFIX
    smoke = "--smoke" in sys.argv
    SMOKE_SUFFIX = "_smoke" if smoke else ""
    if "--verdict-only" in sys.argv:
        verdict_only()
        return
    resume = []
    for arg in sys.argv[1:]:
        if arg.startswith("--resume-from="):
            resume = [p for p in arg.split("=", 1)[1].split(",") if p]
    phase = "all"
    for arg in sys.argv[1:]:
        if arg.startswith("--phase="):
            phase = arg.split("=", 1)[1]
    cells_path = os.path.join(REPO, CELLS_ARTIFACT)
    for arg in sys.argv[1:]:
        if arg.startswith("--cells-from="):
            cells_path = arg.split("=", 1)[1]
            if not os.path.isabs(cells_path):
                cells_path = os.path.join(REPO, cells_path)
    log("record 2012 - COVER width law and delta-floor scans (%s, phase=%s)"
        % ("smoke" if smoke else "full", phase))

    cache = Cache()
    for path in resume:
        resume_path = (path if os.path.isabs(path)
                       else os.path.join(REPO, path))
        with open(resume_path, encoding="utf-8") as stream:
            loaded = json.load(stream)
        top_dxi = loaded.get("dxi", DXI)
        for row in loaded["rows"]:
            dxi = row.get("dxi", top_dxi)
            row.setdefault("dxi", dxi)
            cache.rows[cache.key(row["layer"], row["gamma"], row["delta"],
                                 row["scale"], dxi)] = row
        log("resume: %d rows preloaded from %s (no re-measurement)"
            % (len(loaded["rows"]), resume_path))
    if smoke:
        heights = [("committed", r80.GAMMA1), ("ext", r94.G7)]
        control = None
        width_scales = (0.88, 0.90, 0.92)
        floor_scales = (0.90, 0.92)
        floor_deltas = (0.02, 0.10)
    else:
        heights = HEIGHTS
        control = CONTROL
        width_scales = SCALES
        floor_scales = ANCHOR_SCALES
        floor_deltas = FLOOR_DELTAS

    width_map, floor_map, anchors = {}, {}, []
    layer_control = None

    # ------------------------------------------------ stage 1: width law
    if phase in ("all", "width"):
        for layer, gk in (heights + ([control] if control else [])):
            for scale in width_scales:
                cache.get(layer, gk, WIDTH_DELTA, scale)
        for layer, gk in heights:
            width_map["%s:%.6f" % (layer, gk)] = width_reading(cache, layer, gk)
        if control:
            layer_control = {
                "gamma": control[1],
                "ext_bands": width_reading(cache, "ext", control[1])["bands"],
                "committed_bands": width_reading(cache, "committed",
                                                 control[1])["bands"],
                "ext_C": [[row["scale"], row["C"]] for row in
                          cache.slice("ext", control[1], WIDTH_DELTA)],
                "committed_C": [[row["scale"], row["C"]] for row in
                                cache.slice("committed", control[1],
                                            WIDTH_DELTA)],
            }
        if not smoke:
            cache.dump(os.path.join(REPO, "results",
                                    "2012_cover_scans_partial.json"))

    # --------------------------------------- stage 2a: floor, five-point grid
    if phase in ("all", "floor"):
        for layer, gk in heights:
            for delta in floor_deltas:
                for scale in floor_scales:
                    cache.get(layer, gk, delta, scale)
        if control:
            for delta in floor_deltas:
                for scale in floor_scales:
                    cache.get(control[0], control[1], delta, scale)

        # ----------------------------------- stage 2b: sweep the candidates
        for layer, gk in heights:
            hosts_per_delta = {}
            for delta in floor_deltas:
                cells = cache.slice(layer, gk, delta)
                hosts_per_delta[delta] = sum(1 for row in cells if row["host"])
            with_host = [d for d in floor_deltas if hosts_per_delta[d] > 0]
            candidate = with_host[0] if with_host else None
            if candidate is None or candidate > FLOOR_UNIFORM_BAR:
                sweep = [d for d in (0.02, 0.05, candidate)
                         if d is not None]
                if candidate is None and not smoke:
                    log("  %s g=%.4f: no stage-A host anywhere -> full sweep"
                        % (layer, gk))
                    sweep = list(floor_deltas)
                for delta in sweep:
                    for scale in (SCALES if not smoke else width_scales):
                        cache.get(layer, gk, delta, scale)
                hosts_per_delta = {}
                for delta in floor_deltas:
                    cells = cache.slice(layer, gk, delta)
                    hosts_per_delta[delta] = sum(1 for row in cells
                                                 if row["host"])
                with_host = [d for d in floor_deltas if hosts_per_delta[d] > 0]
            floor_map["%s:%.6f" % (layer, gk)] = {
                "layer": layer, "gamma": gk,
                "hosts_per_delta": hosts_per_delta,
                "deltas_with_host": with_host,
                "floor": (with_host[0] if with_host else None),
            }
            log("  floor %s g=%.4f -> %s (hosts %s)"
                % (layer, gk, floor_map["%s:%.6f" % (layer, gk)]["floor"],
                   {round(k, 2): v for k, v in hosts_per_delta.items()}))
        if not smoke:
            cache.dump(os.path.join(REPO, "results",
                                    "2012_cover_scans_partial.json"))

    # ------------------------------------ record-2019 M1: edges at dxi 0.002
    if phase == "edges":
        with open(cells_path, encoding="utf-8") as stream:
            cells_2019 = json.load(stream)
        m1_cells = cells_2019["m1"]["cells"]
        if smoke:
            m1_cells = m1_cells[:4]
        for cell in m1_cells:
            cache.get(cell["layer"], cell["gamma"], cell["delta"],
                      cell["scale"], dxi=EDGE_DXI)
            if len(cache.rows) % CHECKPOINT_EVERY == 0:
                cache.dump(os.path.join(
                    REPO, "results",
                    "2019_band_edges_partial%s.json" % SMOKE_SUFFIX))
        log("edges: %d cells at dxi=%.4f measured" % (len(m1_cells), EDGE_DXI))

    # ---------------------------------- record-2019 M2: finer delta grid
    if phase == "floor2":
        with open(cells_path, encoding="utf-8") as stream:
            cells_2019 = json.load(stream)
        slots = [(cells_2019["m2"]["slots"][key]["layer"],
                  cells_2019["m2"]["slots"][key]["gamma"])
                 for key in sorted(cells_2019["m2"]["slots"])]
        five_point = [round(p, 6) for p in cells_2019["m2"]["five_point"]]
        if smoke:
            slots = slots[:1]
            five_point = five_point[:1]
        for layer, gk in slots:
            for delta in REFINED_DELTAS:
                for sc in five_point:
                    cache.get(layer, gk, delta, sc)
                    if len(cache.rows) % CHECKPOINT_EVERY == 0:
                        cache.dump(os.path.join(
                            REPO, "results",
                            "2019_floor_refined_partial%s.json"
                            % SMOKE_SUFFIX))
        for layer, gk in slots:
            hosts = [row["host"] for delta in REFINED_DELTAS
                     for row in cache.slice(layer, gk, delta, dxi=DXI)]
            if not any(hosts):
                log("  floor2 %s: no stage-A host at the new deltas -> "
                    "sweep delta=%.3f" % ("%s:%.6f" % (layer, gk),
                                          REFINED_DELTAS[0]))
                for sc in SCALES:
                    cache.get(layer, gk, REFINED_DELTAS[0], sc)
                    if len(cache.rows) % CHECKPOINT_EVERY == 0:
                        cache.dump(os.path.join(
                            REPO, "results",
                            "2019_floor_refined_partial%s.json"
                            % SMOKE_SUFFIX))
        cache.dump(os.path.join(REPO, "results",
                                "2019_floor_refined_partial%s.json"
                                % SMOKE_SUFFIX))

    # --------------------------------------------------------- anchors (K1)
    anchors = anchor_block(cache, force=(phase in ("edges", "floor2")))

    if phase == "edges":
        cache.dump(os.path.join(REPO, "results",
                                "2019_band_edges_rows%s.json" % SMOKE_SUFFIX),
                   status="FULL")
        edges_reading(cache, cells_path, anchors)
        return
    if phase == "floor2":
        cache.dump(os.path.join(REPO, "results",
                                "2019_floor_refined_rows%s.json"
                                % SMOKE_SUFFIX), status="FULL")
        floor2_reading(cache, cells_path, anchors)
        return

    # ----------------------------------------------------------- verdicts
    # The registered width verdict is over the eight registered heights
    # (gamma_1..gamma_6 committed layer, gamma_7/gamma_8 EXT).  The gamma_5 EXT
    # layer control is the same height measured through the other layer, so it
    # is reported as a control (section A2) and kept OUT of the "every height"
    # clause: letting it in would double-count gamma_5 and let the layer
    # question decide the window law.
    control_key = ("ext:%.6f" % LAYER_CONTROL) if control else None
    verdict_windows = {key: entry for key, entry in width_map.items()
                       if key != control_key}
    w7 = width_map.get("ext:%.6f" % r94.G7, {}).get("width_steps")
    w8 = width_map.get("ext:%.6f" % r94.G8, {}).get("width_steps")
    w1 = width_map.get("committed:%.6f" % r80.GAMMA1, {}).get("width_steps")
    if width_map:
        if all(entry["width_steps"] >= WIDTH_STABLE_STEPS
               and entry["n_bands"] <= 1
               for entry in verdict_windows.values()):
            window_verdict = "WINDOW_STABLE"
        elif (w7 is not None and w8 is not None and w1 is not None
              and w7 <= WIDTH_PINCH_STEPS and w8 <= WIDTH_PINCH_STEPS
              and w1 >= WIDTH_ANCHOR_STEPS):
            window_verdict = "WINDOW_PINCHING"
        else:
            window_verdict = "KNOT_COMPLEX"
    else:
        window_verdict = None

    f1 = floor_map.get("committed:%.6f" % r80.GAMMA1, {}).get("floor")
    f7 = floor_map.get("ext:%.6f" % r94.G7, {}).get("floor")
    f8 = floor_map.get("ext:%.6f" % r94.G8, {}).get("floor")
    if floor_map:
        known = [entry["floor"] for entry in floor_map.values()]
        if all(v is not None and v <= FLOOR_UNIFORM_BAR for v in known):
            floor_verdict = "FLOOR_UNIFORM"
        elif f1 is not None and ((f7 is not None and f7 > f1)
                                 or (f8 is not None and f8 > f1)):
            floor_verdict = "FLOOR_RISING"
        else:
            floor_verdict = "FLOOR-MIXED"
    else:
        floor_verdict = None

    verdict = "SMOKE" if smoke else "/".join(
        part for part in (window_verdict, floor_verdict) if part)
    log("=" * 96)
    for key, entry in sorted(width_map.items()):
        log("  width %-28s bands=%d width=%d host_runs=%d"
            % (key, entry["n_bands"], entry["width_steps"],
               entry["n_host_runs"]))
    for key, entry in sorted(floor_map.items()):
        log("  floor %-28s floor=%s" % (key, entry["floor"]))
    log("layer control: %s" % json.dumps(layer_control))
    log("VERDICT: %s" % verdict)

    campaigns = {"committed": list(COMMITTED_HEIGHTS),
                 "ext": list(EXT_HEIGHTS) + [LAYER_CONTROL]}
    suffix = "_smoke" if smoke else ""
    rows = list(cache.rows.values())
    if width_map:
        out = os.path.join(REPO, "results",
                           "2012_cover_window_law%s.json" % suffix)
        with open(out, "w", encoding="utf-8") as stream:
            json.dump({"record": "2012", "scan": "width-law",
                       "width_delta": WIDTH_DELTA,
                       "scales": list(width_scales),
                       "verdict": window_verdict, "windows": width_map,
                       "verdict_keys": sorted(verdict_windows),
                       "control_key": control_key,
                       "layer_control_width": width_map.get(control_key),
                       "anchors": anchors, "layer_control": layer_control,
                       "layer_campaigns": campaigns}, stream, indent=2)
            stream.write("\n")
        log("results -> %s" % out)
    if floor_map:
        out = os.path.join(REPO, "results",
                           "2012_cover_delta_floor%s.json" % suffix)
        with open(out, "w", encoding="utf-8") as stream:
            json.dump({"record": "2012", "scan": "delta-floor",
                       "deltas": list(floor_deltas), "floors": floor_map,
                       "verdict": floor_verdict, "anchors": anchors,
                       "layer_campaigns": campaigns}, stream, indent=2)
            stream.write("\n")
        log("results -> %s" % out)
    out = os.path.join(REPO, "results",
                       "2012_cover_scan_rows%s.json" % suffix)
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2012",
                   "status": "SMOKE" if smoke else "FULL",
                   "dxi": DXI, "rows": rows}, stream, indent=2)
        stream.write("\n")
    log("results -> %s" % out)


if __name__ == "__main__":
    main()