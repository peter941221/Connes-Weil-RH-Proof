#!/usr/bin/env python3
"""Record 2033 P4b + P5: Route-B gate/tail pairing and the lambda screen.

Pre-registered in docs/proofs/2033_gate_tail_pairing_preregistration.md.

Input artifact: results/2032_gate_row_search.json (the P4 gate readings).
Nothing here measures a new gate entry; the decay constants are the only new
numbers, and they are computed exactly as the record-2028 decay block does.
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
import fourpoint_powered_seed_1981 as powered  # noqa: E402

T0 = time.time()
Q = 2.0 ** -14
Q_HALF = 0.5
TWO_PI_12 = (2.0 * math.pi) ** 12
HEIGHT_MAX = 200.0
HEIGHT_NT = 401
SIGMAS = (0.0, 0.5, 1.0)
SMOKE = bool(os.environ.get("RH_PAIRING_SMOKE"))

# the reference owner plus every (gamma, N) that carries a gate row at n >= 1
OWNERS = [
    (14.134725141734693, 4),
    (21.022039638771556, 3), (21.022039638771556, 4), (21.022039638771556, 5),
    (30.424876125859513, 3), (30.424876125859513, 4), (30.424876125859513, 5),
]
if SMOKE:
    OWNERS = [(14.134725141734693, 4), (30.424876125859513, 4)]


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def decay_constants(rho, N, seed_transform, seed0,
                    height_max=HEIGHT_MAX, nt=HEIGHT_NT):
    owner, targets, radius, known = op.build_owner(rho, N)
    values = [op.target_value(rho, z) for z in owner]
    base_values = [1.0 + 0j] * len(targets)
    heights = np.linspace(0.0, height_max, nt)
    c4 = c2 = cc2 = 0.0
    for sigma in SIGMAS:
        s = sigma + 1j * heights
        lb = op.cardinal_transform(targets, base_values, seed0, s, seed_transform)
        lc = op.cardinal_transform(owner, values, seed0, s, seed_transform)
        scaled = np.abs(heights / (2.0 * math.pi))
        c4 = max(c4, float(np.max(scaled ** 4 * np.abs(lb))))
        c2 = max(c2, float(np.max(scaled ** 2 * np.abs(lb))))
        cc2 = max(cc2, float(np.max(scaled ** 2 * np.abs(lc))))
    return {"owner_cardinality": len(owner), "known_zero_count": len(known),
            "radius": radius, "base_C4": c4, "base_C2": c2,
            "correction_C2": cc2}


def tail_q(H, c4, c2, lam, n, q):
    """tau(n, lam) = H^4 (2 pi)^12 (C4 C2)^2 q^(2n) (1 + H^4/|lam|)^2."""
    if lam == 0:
        return float("inf")
    a0 = H ** 4 * TWO_PI_12 * (c4 * c2) ** 2
    return a0 * q ** (2 * n) * (1.0 + H ** 4 / abs(lam)) ** 2


def tail_q_inf(H, c4, c2, n, q):
    a0 = H ** 4 * TWO_PI_12 * (c4 * c2) ** 2
    return a0 * q ** (2 * n)


def lam_min_for_tail(H, c4, c2, n, q):
    """Smallest |lam| with tau(n, lam) < 1, or None when it never happens."""
    a0 = H ** 4 * TWO_PI_12 * (c4 * c2) ** 2
    lim = a0 * q ** (2 * n)
    if lim >= 1.0:
        return None
    return H ** 4 / (1.0 / math.sqrt(lim) - 1.0)


def main():
    report = {
        "record": 2033,
        "phase": "P4b gate/tail pairing + P5 lambda screen",
        "status": "PENDING",
        "preregistration":
            "docs/proofs/2033_gate_tail_pairing_preregistration.md",
        "q": Q,
        "q_half_control": Q_HALF,
        "decay_grid": {"height_max": HEIGHT_MAX, "nt": HEIGHT_NT,
                       "sigmas": list(SIGMAS)},
        "source_artifact": "results/2032_gate_row_search.json",
    }
    gates = json.loads((ROOT / "results" / "2032_gate_row_search.json").read_text())
    gate_index = {(r["gamma"], r["N"], r["n"]): r for r in gates["rows"]}
    report["p4_gate_status"] = gates["status"]
    report["p4_cutoff_label"] = gates["cutoff_label"]

    seed_transform = powered.make_powered_seed(order=scan.SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])

    # ------------------------------------------------------------- P4b block
    log("P4b: decay constants and the gate/tail pairing")
    paired, owners_block = [], []
    for gamma, N in OWNERS:
        rho = complex(0.55, gamma)
        dec = decay_constants(rho, N, seed_transform, seed0)
        dec1981 = decay_constants(rho, N, seed_transform, seed0,
                                  height_max=160.0, nt=321)
        H = 3.0 + abs(rho)
        rows = []
        for n in range(5):
            g = gate_index.get((gamma, N, n))
            if g is None:
                continue
            pc = g["dxi0.02"]
            lam = pc["lambda"]
            tau_q = tail_q(H, dec["base_C4"], dec["correction_C2"], lam, n, Q)
            tau_half = tail_q(H, dec1981["base_C4"], dec1981["correction_C2"],
                              lam, n, Q_HALF)
            tau_inf = tail_q_inf(H, dec["base_C4"], dec["correction_C2"], n, Q)
            lmin = lam_min_for_tail(H, dec["base_C4"], dec["correction_C2"], n, Q)
            row = {
                "n": n, "C": pc["C"], "b": pc["b"], "det": pc["det"],
                "lambda": lam, "gate_signs": bool(g["gate_signs"]),
                "tau_q": tau_q, "tau_q_no_vertex_factor": tau_inf,
                "tau_half_control": tau_half,
                "tail_closed_q": bool(tau_q < 1.0),
                "lambda_min_for_tail": lmin,
                "gate_and_tail": bool(g["gate_signs"] and tau_q < 1.0),
            }
            rows.append(row)
            log("  gamma=%7.3f N=%d n=%d gate=%s tau_q=%.3e tau_half=%.3e "
                "paired=%s" % (gamma, N, n, g["gate_signs"], tau_q, tau_half,
                               row["gate_and_tail"]))
        owners_block.append({
            "gamma": gamma, "N": N, "H": H, "decay": dec,
            "decay_1981_grid": dec1981,
            "A0": H ** 4 * TWO_PI_12 * (dec["base_C4"] * dec["correction_C2"]) ** 2,
            "rows": rows})
        paired += [{"gamma": gamma, "N": N, "n": r["n"]}
                   for r in rows if r["gate_and_tail"]]
    report["owners"] = owners_block
    report["paired_rows"] = paired

    # reproduction anchor against the committed record-1981 proxy
    ref = json.loads(
        (ROOT / "results" / "1981_powered_seed_underapprox.json").read_text())
    own = next(o for o in owners_block
               if o["gamma"] == 14.134725141734693 and o["N"] == 4)
    anchor = []
    for row in own["rows"]:
        committed = next((it for it in ref["rows"] if it["n"] == row["n"]), None)
        if committed is None:
            continue
        anchor.append({"n": row["n"],
                       "tau_half_here": row["tau_half_control"],
                       "committed_1981": committed["tail_proxy_L_over_lambda_sq"],
                       "dev": abs(row["tau_half_control"] /
                                  committed["tail_proxy_L_over_lambda_sq"] - 1.0)})
    report["anchor_1981_tail_proxy"] = anchor
    report["anchor_1981_max_dev"] = (max(a["dev"] for a in anchor) if anchor
                                     else None)
    log("anchor vs record-1981 tail proxy: max dev %s (expected: the 1981"
        " lambda_n are the withdrawn dxi=0.05 rows)" %
        report["anchor_1981_max_dev"])

    # the converged-grid anchor: record-2028 trend rows use the same decay
    # constants and the dxi = 0.02 vertex lambda.
    trend = json.loads(
        (ROOT / "results" / "2028_coupling_scan.json").read_text())["trend"]
    anchor28 = []
    for row in own["rows"]:
        committed = next((it for it in trend if it["n"] == row["n"]), None)
        if committed is None or committed.get("tail_proxy_L_over_lambda_sq") is None:
            continue
        anchor28.append({"n": row["n"], "tau_half_here": row["tau_half_control"],
                         "committed_2028":
                             committed["tail_proxy_L_over_lambda_sq"],
                         "dev": abs(row["tau_half_control"] /
                                    committed["tail_proxy_L_over_lambda_sq"] - 1.0)})
    report["anchor_2028_tail_proxy"] = anchor28
    report["anchor_2028_max_dev"] = (max(a["dev"] for a in anchor28)
                                     if anchor28 else None)
    log("anchor vs record-2028 (converged) tail proxy: max dev %s" %
        report["anchor_2028_max_dev"])

    # derived closure index: the exact n-step factor of tau_inf is q^2
    log("derived closure index from tau_inf < 1 (no new measurement)")
    for o in owners_block:
        a0 = o["A0"]
        nmin = (math.ceil(math.log(a0) / (2.0 * math.log(1.0 / Q)))
                if a0 > 1.0 else 0)
        o["n_min_lambda_inf_tail"] = int(nmin)
        s_n = 2.0 * (nmin + 2)
        if nmin <= 7:
            vals, _ = scan.fast_prime_powers_up_to(math.exp(s_n))
            o["prime_book_at_n_min"] = int(vals.size)
            o["prime_book_measurement"] = "sieved"
        else:
            o["prime_book_at_n_min"] = float(math.exp(s_n) / s_n)
            o["prime_book_measurement"] = "PNT envelope, not sieved"
        o["certified_route_at_n_min"] = bool(
            o["prime_book_at_n_min"] <= 60000)
        log("  gamma=%7.3f N=%d A0=%.3e n_min=%d P_nmin=%s certified=%s" % (
            o["gamma"], o["N"], a0, nmin, o["prime_book_at_n_min"],
            o["certified_route_at_n_min"]))

    # -------------------------------------------------------------- P5 block
    log("P5: non-vertex lambda screen (exact parabola, closed form)")
    lam_scan = np.logspace(0.0, 30.0, 121)
    lam_block = []
    for gamma, N in OWNERS:
        rho = complex(0.55, gamma)
        dec = next(o["decay"] for o in owners_block
                   if o["gamma"] == gamma and o["N"] == N)
        H = 3.0 + abs(rho)
        rows = []
        for n in range(5):
            g = gate_index.get((gamma, N, n))
            if g is None:
                continue
            pc = g["dxi0.02"]
            C, b, D = pc["C"], pc["b"], pc["D"]
            B = 2.0 * b
            disc = B * B - 4.0 * C * D
            entry = {"n": n, "C_sign": bool(C > 0), "disc": disc,
                     "gate_signs": bool(g["gate_signs"])}
            if C != 0 and disc >= 0:
                sq = math.sqrt(disc)
                entry["roots"] = [(B - sq) / (2 * C), (B + sq) / (2 * C)]
            else:
                entry["roots"] = None
            lmin = lam_min_for_tail(H, dec["base_C4"], dec["correction_C2"], n, Q)
            entry["lambda_min_for_tail"] = lmin
            # joint set on the registered scan
            joint = []
            for lam in lam_scan:
                gate_val = D - lam * B + lam * lam * C
                tau = tail_q(H, dec["base_C4"], dec["correction_C2"], lam, n, Q)
                if gate_val < 0.0 and tau < 1.0:
                    joint.append(float(lam))
            entry["joint_set_log10_range"] = ([math.log10(joint[0]),
                                              math.log10(joint[-1])]
                                             if joint else None)
            entry["joint_set_nonempty"] = bool(joint)
            rows.append(entry)
            log("  gamma=%7.3f N=%d n=%d C%s roots=%s joint=%s" % (
                gamma, N, n, "+" if C > 0 else "-",
                None if entry["roots"] is None
                else "[%.3e, %.3e]" % tuple(entry["roots"]),
                entry["joint_set_log10_range"]))
        lam_block.append({"gamma": gamma, "N": N, "rows": rows})
    report["lambda_screen"] = lam_block
    report["lambda_joint_rows"] = [
        {"gamma": o["gamma"], "N": o["N"], "n": r["n"]}
        for o in lam_block for r in o["rows"] if r["joint_set_nonempty"]]

    # ------------------------------------------------------------- verdicts
    if paired:
        report["status"] = "PAIR-FOUND"
    else:
        report["status"] = "PAIR-MISMATCH"
    report["lambda_status"] = ("LAMBDA-PAYS"
                               if report["lambda_joint_rows"]
                               else "LAMBDA-CANNOT-PAY")

    out = ROOT / "results" / "2033_gate_tail_pairing.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log("wrote %s" % out)
    print(json.dumps({"status": report["status"],
                      "paired_rows": report["paired_rows"],
                      "lambda_status": report["lambda_status"],
                      "lambda_joint_rows": report["lambda_joint_rows"],
                      "anchor_2028_max_dev": report["anchor_2028_max_dev"],
                      "n_min_lambda_inf_tail": [
                          {"gamma": o["gamma"], "N": o["N"],
                           "n_min": o["n_min_lambda_inf_tail"],
                           "P_nmin": o["prime_book_at_n_min"],
                           "certified": o["certified_route_at_n_min"]}
                          for o in owners_block]},
                     indent=2))


if __name__ == "__main__":
    main()
