#!/usr/bin/env python3
"""Record 2011: A-HD constrained health-maximization desk.

Pre-registered in docs/proofs/2011_route_a_ahd_dual_desk_preregistration.md
(committed before this run).  The owner, family, fibre basis and readout are
the record-2006 cone-layer ones, imported directly from
`routea_health_cone_2006` so no second copy of the machinery can drift; the
only new layer here is the driver: an amplitude grid extended past the
record-2004/2010 range, the constrained maximization, the resolution-stability
re-read (J4) and the conditional stage 2.

No theorem, no Lean brick, no RH claim.
"""

import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routea_opposite_gates_height_1994 as r94  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import routea_health_cone_2006 as r06  # noqa: E402

T0 = time.time()
CASES = [
    (0.10, r94.G5, 0.92, "G5-H"),
    (0.10, r94.G5, 0.90, "G5-W"),
    (0.10, r94.G7, 0.92, "G7-H"),
    (0.10, r94.G8, 0.88, "G8-H"),
]
RANKS = (1, 2, 4, 6)
SIGMAS = (0.05, 0.10, 0.20, 0.40, 0.80, 1.20, 1.60)
STAGE2_SCALES = (0.86, 0.88, 0.90, 0.92, 0.94)
GAIN_BAR = 2.0
NOGAIN_BAR = 1.2
J4_DXI = 0.004
J4_BAR = 5.0e-3
# ---------------------------------------------------------------------------
# Amendment 2014a (registered before this mode is run): the original J1 gated
# the cross-resolution offset of BOTH C and D at 5e-3.  The committed cone
# instrument (record 2006, same dxi = 0.008 as this desk) gated D only, at
# 1e-3, and REPORTED the C offset: C is the f-cancelled coordinate
# (f = mm / A, record 2010 section 4), so a fixed-resolution offset on C is a
# property of the owner, not a machinery error.  The amended gate is the
# record-2006 gate, plus the stronger layer check that the sigma = 0 row
# equals the committed cone anchor row on both entries.
ANCHOR_BAND_AMENDED = 1.0e-3
LAYER_BAR = 1.0e-9
LAYER_ANCHORS = {
    "G5-H": (+1.49089499804813386e+00, -6.30752072626298047e+12),
    "G5-W": (+2.50171187903106329e-01, -2.25136825561206312e+14),
    "G7-H": (+1.73154001136437728e+02, -2.03596080584510210e+20),
    "G8-H": (+6.64107474896016356e+02, -1.11126519153653187e+20),
}
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def setup_case(delta, gamma, scale, tag):
    """Build the record-2006 owner layer for one (delta, gamma, scale)."""
    rho = (0.5 + delta) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam, base_fam = r06.two_copy_family(nodes, scale, gamma)
    xw = r80.family_quad(fam, r06.K)
    base_ref, corr_ref, amp = r80.amplitudes(
        nodes, values, base_fam, r06.K, r80.family_quad(base_fam, r06.K))
    cond = max(amp["base"]["cond"], amp["corr"]["cond"])
    gram = r06.h1_gram(fam)
    matrix = r80.family_values(fam, r06.K, np.asarray(nodes, dtype=complex),
                               xw).T
    base = r06.embedded_reference(base_ref)
    corr = r06.embedded_reference(corr_ref)
    e_ref = r06.h1_norm(corr, gram)
    dirs, spec = r06.feasible_directions(fam, gram, matrix, RANKS)
    return {
        "tag": tag, "delta": delta, "gamma": gamma, "scale": scale, "rho": rho,
        "nodes": nodes, "values": values, "fam": fam, "xw": xw, "base": base,
        "corr": corr, "e_ref": e_ref, "cond": cond, "dirs": dirs,
        "spectrum": spec["spectrum"], "nullity": spec["nullity"],
        "support_radius": max(a for a, _ in fam) * (r06.N + 2),
        "basis_size": len(fam),
    }


def measure_rows(env, ranks, sigmas, dxi=None):
    """Measure the registered grid for one owner environment."""
    saved = r06.DXI
    if dxi is not None:
        r06.DXI = dxi
    try:
        anchor = r06.measure(env["nodes"], env["values"], env["rho"],
                             env["delta"], env["fam"], env["xw"], env["base"],
                             env["corr"], env["cond"], 0, 0.0)
        rows = []
        for want in ranks:
            for sigma in sigmas:
                corr = env["corr"] + sigma * env["e_ref"] * env["dirs"][want]
                rows.append(r06.measure(env["nodes"], env["values"], env["rho"],
                                        env["delta"], env["fam"], env["xw"],
                                        env["base"], corr, env["cond"], want,
                                        sigma))
    finally:
        r06.DXI = saved
    return anchor, rows


def rule_maximiser(anchor, rows):
    """The registered rule: max C over certified rows with D < 0."""
    best = None
    for row in rows:
        if not row["certified"] or not (row["D"] < 0.0):
            continue
        if not (anchor["C"] > 0.0):
            continue
        ratio = row["C"] / anchor["C"]
        if best is None or ratio > best[0]:
            best = (ratio, row)
    if best is None:
        return None, None, None
    return best[0], best[1], (best[1]["rank"], best[1]["sigma"])


def resolution_stability(env, row):
    """J4: re-read the maximising configuration at half the resolution."""
    corr = env["corr"] + row["sigma"] * env["e_ref"] * env["dirs"][row["rank"]]
    saved = r06.DXI
    r06.DXI = J4_DXI
    try:
        again = r06.measure(env["nodes"], env["values"], env["rho"], env["delta"],
                            env["fam"], env["xw"], env["base"], corr,
                            env["cond"], row["rank"], row["sigma"])
    finally:
        r06.DXI = saved
    sign_same = bool(np.sign(again["C"]) == np.sign(row["C"]))
    health_same = bool(again["healthy"] == row["healthy"])
    c_shift = abs(again["C"] - row["C"]) / max(abs(row["C"]), 1e-300)
    d_shift = abs(again["D"] - row["D"]) / max(abs(row["D"]), 1e-300)
    return {
        "dxi": J4_DXI, "C": again["C"], "D": again["D"], "det": again["det"],
        "certified": again["certified"], "healthy": again["healthy"],
        "sign_same": sign_same, "health_same": health_same,
        "C_rel_shift": c_shift, "D_rel_shift": d_shift,
        "pass": bool(sign_same and health_same),
    }


def pearson(xs, ys):
    if len(xs) < 2:
        return None
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    dx = math.sqrt(sum((x - mx) ** 2 for x in xs))
    dy = math.sqrt(sum((y - my) ** 2 for y in ys))
    if dx == 0.0 or dy == 0.0:
        return None
    return num / (dx * dy)


def census(anchor, rows, tag):
    """R1-R4 secondary readings over one owner's registered grid."""
    xs, ys = [], []
    improving = []
    for row in rows:
        if not row["certified"]:
            continue
        xs.append(row["C"] / anchor["C"])
        ys.append(abs(row["D"]) / max(abs(anchor["D"]), 1e-300))
        if row["C"] > anchor["C"]:
            ident = row["identity"] or {}
            improving.append({
                "rank": row["rank"], "sigma": row["sigma"],
                "C_ratio": row["C"] / anchor["C"],
                "D_abs_ratio": abs(row["D"]) / max(abs(anchor["D"]), 1e-300),
                "f_ratio": (abs(ident["f"]) / abs(anchor["identity"]["f"])
                            if ident.get("f") and anchor["identity"].get("f")
                            else None),
                "healthy": row["healthy"], "det": row["det"],
            })
    return {
        "tag": tag,
        "corr_C_response_D_response": pearson(xs, ys),
        "n_rows_used": len(xs),
        "n_improving_rows": len(improving),
        "improving_rows": improving,
        "D_abs_response_min": min(ys) if ys else None,
        "D_abs_response_max": max(ys) if ys else None,
    }


def tail_reading(rows):
    """R3: does C keep increasing over the last two registered amplitudes?"""
    by_rank = {}
    for row in rows:
        by_rank.setdefault(row["rank"], []).append(row)
    out = {}
    for rank, group in by_rank.items():
        group.sort(key=lambda r: r["sigma"])
        last, prev = group[-1], group[-2]
        out[str(rank)] = {
            "sigma_last": last["sigma"], "C_last": last["C"],
            "sigma_prev": prev["sigma"], "C_prev": prev["C"],
            "C_still_increasing": bool(last["C"] > prev["C"]),
        }
    return out


def run_case(delta, gamma, scale, tag, anchors):
    log("case %s (delta %.2f gamma %.4f scale %.2f)" % (tag, delta, gamma,
                                                       scale))
    env = setup_case(delta, gamma, scale, tag)
    anchor, rows = measure_rows(env, RANKS, SIGMAS)
    ref = anchors.get(tag)
    dev = {}
    if ref:
        for key in ("C", "D"):
            dev[key] = abs(anchor[key] - float(ref[key])) \
                / max(abs(float(ref[key])), 1e-300)
    log("  anchor C=%+.6e D=%+.6e cert=%s dev_C=%.2e dev_D=%.2e"
        % (anchor["C"], anchor["D"], anchor["certified"],
           dev.get("C", float("nan")), dev.get("D", float("nan"))))
    gain, best, where = rule_maximiser(anchor, rows)
    j4 = None
    if best is not None:
        j4 = resolution_stability(env, best)
        log("  rule max rank=%d sigma=%.2f C=%+.6e D=%+.6e ratio=%.3f "
            "healthy=%s | J4 sign_same=%s health_same=%s dC=%.1e dD=%.1e"
            % (best["rank"], best["sigma"], best["C"], best["D"], gain,
               best["healthy"], j4["sign_same"], j4["health_same"],
               j4["C_rel_shift"], j4["D_rel_shift"]))
    else:
        log("  rule max: none (no certified row with D < 0 and C(0) > 0)")
    return {
        "tag": tag, "delta": delta, "gamma": gamma, "scale": scale,
        "basis_size": env["basis_size"], "cond": env["cond"],
        "nullity": env["nullity"], "support_radius": env["support_radius"],
        "e_ref": env["e_ref"], "reference_dev": dev, "anchor": anchor,
        "gain": gain, "argmax": ({"rank": where[0], "sigma": where[1]}
                                 if where else None),
        "argmax_row": best, "j4": j4,
        "census": census(anchor, rows, tag),
        "tail_reading": tail_reading(rows),
        "rows": rows,
    }


def stage2(tag, delta, gamma):
    """Conditional stage 2: the same rule at five scales."""
    log("stage 2 at %s (delta %.2f gamma %.4f)" % (tag, delta, gamma))
    cells = []
    for sc in STAGE2_SCALES:
        env = setup_case(delta, gamma, sc, tag)
        anchor, rows = measure_rows(env, RANKS, SIGMAS)
        gain, best, where = rule_maximiser(anchor, rows)
        cells.append({
            "scale": sc, "anchor": anchor,
            "gain": gain,
            "argmax": ({"rank": where[0], "sigma": where[1]} if where else None),
            "argmax_row": best,
            "committed_healthy": bool(anchor["healthy"]),
            "committed_certified": bool(anchor["certified"]),
            "committed_C": anchor["C"],
        })
        log("  sc=%.2f committed C=%+.4e healthy=%s | rule gain=%s healthy=%s"
            % (sc, anchor["C"], anchor["healthy"],
               "%.3f" % gain if gain is not None else "none",
               best["healthy"] if best is not None else None))
        partial = os.path.join(REPO, "results",
                               "2011_route_a_ahd_dual_partial.json")
        with open(partial, "w", encoding="utf-8") as stream:
            json.dump({"record": "2011", "status": "PARTIAL_STAGE2",
                       "owner": tag, "cells": cells}, stream, indent=2)
            stream.write("\n")
    return {"owner": tag, "cells": cells}


def stage2_verdict(cells):
    rule_run = [c["scale"] for c in cells
                if c["argmax_row"] is not None and c["argmax_row"]["healthy"]]
    committed_run = [c["scale"] for c in cells
                     if c["committed_healthy"]]
    n_rule, n_comm = len(rule_run), len(committed_run)
    if n_rule >= n_comm + 2:
        verdict = "A-HD-WINDOW-WIDENS"
    elif n_rule == n_comm and rule_run != committed_run:
        verdict = "A-HD-WINDOW-SHIFTS"
    elif n_rule == n_comm:
        verdict = "A-HD-WINDOW-SHIFTS" if rule_run != committed_run \
            else "A-HD-WINDOW-SAME"
    else:
        verdict = "A-HD-WINDOW-NARROWS"
    return {
        "verdict": verdict,
        "rule_run": rule_run, "committed_run": committed_run,
        "n_rule": n_rule, "n_committed": n_comm,
    }


def main():
    smoke = "--smoke" in sys.argv
    # `--reduce` recomputes the registered verdict from the checkpoint written
    # by the measurement pass.  It exists because the driver's verdict block
    # raised a TypeError (a boolean treated as an iterable in the j4
    # aggregation) after all four cases had already been measured and
    # checkpointed: the measurement is complete and the fix touches only the
    # type of that aggregation, so no row is re-measured and no threshold is
    # touched.
    reduce_only = "--reduce" in sys.argv
    amended = "--amended-anchor" in sys.argv
    partial = os.path.join(REPO, "results",
                           "2011_route_a_ahd_dual_partial.json")
    if reduce_only:
        with open(partial, encoding="utf-8") as stream:
            records = json.load(stream)["cases"]
        log("reduce from checkpoint: %d cases, %d rows"
            % (len(records), sum(len(rec["rows"]) for rec in records)))
    else:
        cases = CASES[:1] if smoke else CASES
        anchors = r06.load_anchors()
        records = []
        for case in cases:
            records.append(run_case(*case[:3], case[3], anchors))
            if not smoke:
                with open(partial, "w", encoding="utf-8") as stream:
                    json.dump({"record": "2011", "status": "PARTIAL",
                               "cases": records}, stream, indent=2)
                    stream.write("\n")

    checks = []
    for rec in records:
        dev = rec["reference_dev"]
        anchor_ok = bool(rec["anchor"]["certified"]
                         and dev.get("D", 0.0) <= J4_BAR
                         and dev.get("C", 0.0) <= J4_BAR)
        rows_ok = all(r["certified"] for r in rec["rows"])
        ident_ok = all(
            (not r["identity"])
            or (r["identity"]["dev_var"] <= 5.0e-3
                and r["identity"]["dev_moment"] <= 5.0e-3
                and r["identity"]["dev_alg"] <= 1.0e-9)
            for r in rec["rows"])
        j4_ok = rec["j4"]["pass"] if rec["j4"] else None
        layer_ref = LAYER_ANCHORS.get(rec["tag"])
        layer_dev = {}
        if layer_ref:
            for key, ref in zip(("C", "D"), layer_ref):
                layer_dev[key] = abs(rec["anchor"][key] - ref) / abs(ref)
        amended_ok = bool(rec["anchor"]["certified"]
                          and dev.get("D", 1.0) <= ANCHOR_BAND_AMENDED
                          and layer_dev
                          and max(layer_dev.values()) <= LAYER_BAR)
        checks.append({"tag": rec["tag"], "anchor_ok": anchor_ok,
                       "anchor_ok_amended": amended_ok,
                       "rows_ok": rows_ok, "identity_ok": ident_ok,
                       "j4_ok": j4_ok,
                       "anchor_dev_C": dev.get("C"), "anchor_dev_D": dev.get("D"),
                       "layer_dev_C": layer_dev.get("C"),
                       "layer_dev_D": layer_dev.get("D")})

    gains = [(rec["tag"], rec["gain"]) for rec in records
             if rec["gain"] is not None]
    n_gain = sum(1 for item in gains if item[1] >= GAIN_BAR)
    ok_key = "anchor_ok_amended" if amended else "anchor_ok"
    if smoke:
        verdict = "SMOKE"
    elif not all(c[ok_key] and c["rows_ok"] and c["identity_ok"]
                 and (c["j4_ok"] in (True, None)) for c in checks):
        verdict = "INSTRUMENT-FAIL"
    elif n_gain >= 2:
        verdict = "A-HD-GAIN"
    elif all(item[1] < NOGAIN_BAR for item in gains) and gains:
        verdict = "A-HD-NOGAIN"
    else:
        verdict = "A-HD-MIXED"

    stage2_out = None
    if not smoke and verdict == "A-HD-GAIN":
        winner = max(gains, key=lambda item: item[1])[0]
        rec = [r for r in records if r["tag"] == winner][0]
        cells = stage2(winner, rec["delta"], rec["gamma"])
        stage2_out = {"owner": winner, "cells": cells}
        stage2_out.update(stage2_verdict(cells))
        verdict += "/" + stage2_out["verdict"]

    corrs = [(rec["tag"], (rec["census"] or {}).get("corr_C_response_D_response"))
             for rec in records]
    log("=" * 96)
    for check, rec in zip(checks, records):
        log("  %s anchor=%s rows=%s ident=%s j4=%s gain=%s argmax=%s"
            % (check["tag"], check["anchor_ok"], check["rows_ok"],
               check["identity_ok"], check["j4_ok"],
               "%.3f" % rec["gain"] if rec["gain"] is not None else None,
               rec["argmax"]))
    log("corr(C response, |D| response) per owner: %s" % corrs)
    log("VERDICT: %s" % verdict)

    suffix = "_smoke" if smoke else ""
    if amended:
        suffix = "_amended"
    out = os.path.join(REPO, "results",
                       "2011_route_a_ahd_dual%s.json" % suffix)
    driver = {
        "mode": "reduce-from-checkpoint" if reduce_only
        else ("smoke" if smoke else "measure"),
        "checkpoint": os.path.relpath(partial, REPO).replace("\\", "/")
        if reduce_only else None,
        "note": ("verdict recomputed from the four measured cases after a "
                 "driver TypeError fix in the j4 aggregation; no row was "
                 "re-measured and no threshold was changed")
        if reduce_only else "single-pass measurement and verdict",
    }
    instrument = {
        "anchor_gate": ("amendment 2014a: D dev <= 1e-3 gated, C dev reported, "
                        "plus the sigma = 0 row equal to the record-2006 "
                        "committed cone anchor within 1e-9 on C and D")
        if amended else
        "registered J1: C dev <= 5e-3 and D dev <= 5e-3, both gated",
        "verdict_key": ok_key,
    }
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2011", "verdict": verdict,
                   "amended": bool(amended), "instrument": instrument,
                   "ranks": list(RANKS), "sigma_grid": list(SIGMAS),
                   "stage2_scales": list(STAGE2_SCALES),
                   "gain_bar": GAIN_BAR, "nogain_bar": NOGAIN_BAR,
                   "driver": driver, "checks": checks, "gains": gains,
                   "stage2": stage2_out, "cases": records},
                  stream, indent=2)
        stream.write("\n")
    log("results -> %s" % out)


if __name__ == "__main__":
    main()