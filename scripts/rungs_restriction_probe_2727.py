#!/usr/bin/env python3
"""Record 2727 probe: does the row-B envelope clear the wired pins with the
rung set restricted to the already-Lean-proved orders?

Decision it settles: whether the D-ladder brick (orders 4..12) is REQUIRED
for the three wired cardinal pins, or whether the proved orders
{1 (exact 2), 2 (exact 8), 3 (bracket [787283384, 787283385]/1e7)} suffice.

Method: re-run the frozen 2720 engine on the stored row B
(`p3.Row_(p3.CANDIDATES[1])`), with a same-run control that the full-table
values reproduce the committed artifact bitwise (`results/2720_...json`
row B certified C4*/C2*/q*).  Then re-run `scan_channel` / `q_star_at`
with every rung k > cut set to `+inf` (min-inert), i.e. effectively
restricted to {1..cut}, for cut in 3..12.  Rung set restriction can only
INCREASE the envelope, so a clearing at a small cut is the strongest
possible reading.

Writes results/2727_rungs_restriction_probe.json.
Usage: python3 scripts/rungs_restriction_probe_2727.py
"""

import hashlib
import importlib.util
import json
import os
import struct
import sys
import time

import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P3 = os.path.join(ROOT, "scripts", "p3_certified_strip_constants_2720.py")
ART2720 = os.path.join(ROOT, "results",
                       "2720_p3_certified_strip_constants.json")
OUT = os.path.join(ROOT, "results", "2727_rungs_restriction_probe.json")

T_START = time.time()
mp.mp.dps = 60  # own context; the p3 load below resets it by design

checks = {}
failures = []


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T_START, msg), flush=True)


def guard(name, ok, detail=""):
    checks[name] = bool(ok)
    if not ok:
        failures.append((name, str(detail)))
    print(("PASS " if ok else "FAIL ") + name
          + (" " + str(detail) if detail else ""), flush=True)


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def bits(a, b):
    """Bitwise binary64 equality (struct compare; False on NaN)."""
    return struct.pack("<d", float(a)) == struct.pack("<d", float(b))


# ---------------------------------------------------------------------------
# S0: load the frozen engine and the stored row B
# ---------------------------------------------------------------------------
p3 = load("p3", P3)
art = json.load(open(ART2720, encoding="utf-8"))
rowB = art["rows"][1]
guard("S0.row_identity",
      rowB["gamma"] == 21.022039638771556 and rowB["N"] == 5,
      str((rowB["gamma"], rowB["N"])))
cert = rowB["certified"]

row = p3.Row_(p3.CANDIDATES[1])
D, ctl = p3.certified_D_table()
cb = p3.make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
cc = p3.make_consts(row.owner, row.values)
guard("S0.consts_counts", (len(cb), len(cc)) == (8, 3),
      "base=%d corr=%d" % (len(cb), len(cc)))

# ---------------------------------------------------------------------------
# S1: same-run control -- full table reproduces the committed artifacts
# ---------------------------------------------------------------------------
sup_b_full, C4_full = p3.scan_channel(cb, 4, D)
sup_c_full, C2_full = p3.scan_channel(cc, 2, D)
q64_full = p3.q_star_at(cb, 64, D)
log("full-table: C4*=%r C2*=%r q*(64)=%r" % (C4_full, C2_full, q64_full))
guard("S1.control_C4_bitwise", bits(C4_full, cert["C4_star"]),
      "%r vs %r" % (C4_full, cert["C4_star"]))
guard("S1.control_C2_bitwise", bits(C2_full, cert["C2_star_corr"]),
      "%r vs %r" % (C2_full, cert["C2_star_corr"]))
guard("S1.control_q_bitwise", bits(q64_full, cert["q_star_T64"]),
      "%r vs %r" % (q64_full, cert["q_star_T64"]))

if failures:
    payload = {"record": 2727, "status": "CONTROL-FAIL",
               "note": "no verdict licensed", "checks": checks,
               "failures": failures}
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(json.dumps(payload, indent=2) + "\n")
    log("CONTROL-FAIL")
    sys.exit(1)

# ---------------------------------------------------------------------------
# S2: restricted-rung sweeps
# ---------------------------------------------------------------------------
PINS = {"C4": 61000000.0, "C2": 29000000.0, "q": 26e-17}
KMAX = p3.K_MAX  # 12


def restrict(kmax_keep):
    return {k: (D[k] if k <= kmax_keep else mp.inf)
            for k in range(1, KMAX + 1)}


sweep = {}
for cut in range(3, KMAX + 1):
    Dr = restrict(cut)
    _sb, C4 = p3.scan_channel(cb, 4, Dr)
    _sc, C2 = p3.scan_channel(cc, 2, Dr)
    q64 = p3.q_star_at(cb, 64, Dr)
    rec = {
        "C4_star": C4, "C4_over_pin": C4 / PINS["C4"],
        "C4_clears": bool(C4 <= PINS["C4"]),
        "C2_star": C2, "C2_over_pin": C2 / PINS["C2"],
        "C2_clears": bool(C2 <= PINS["C2"]),
        "q_star_T64": q64, "q_over_pin": q64 / PINS["q"],
        "q_clears": bool(q64 <= PINS["q"]),
    }
    rec["all_three_clear"] = (rec["C4_clears"] and rec["C2_clears"]
                              and rec["q_clears"])
    sweep["rungs_1_%d" % cut] = rec
    log("rungs<=%2d: C4*/pin=%.6f %s  C2*/pin=%.6f %s  q/pin=%.6f %s"
        % (cut, rec["C4_over_pin"], rec["C4_clears"],
           rec["C2_over_pin"], rec["C2_clears"],
           rec["q_over_pin"], rec["q_clears"]))

first_clear = next((cut for cut in range(3, KMAX + 1)
                    if sweep["rungs_1_%d" % cut]["all_three_clear"]), None)

payload = {
    "record": 2727,
    "date": "2026-10-17",
    "status": "PROBE-OK",
    "verdict": ("RUNGS-RESTRICTED-%s" % ("CLEAR-AT-%d" % first_clear
                                         if first_clear else "NO-CLEAR")),
    "object": ("stored row B (gamma_2, N=5) three wired pins under rung-set "
               "restriction {1..cut}, same-run full-table bitwise control"),
    "pins": PINS,
    "full_table": {"C4_star": C4_full, "C2_star": C2_full,
                   "q_star_T64": q64_full},
    "sweep": sweep,
    "first_clearing_cut": first_clear,
    "checks": checks,
    "failures": failures,
    "nonclaims": [
        "engine-grade measurement, no Lean claim; the D-table stays the "
        "2720 artifact; restriction via +inf is min-inert by construction",
        "no producer GO, no RH claim",
    ],
    "provenance": {
        "checker": {"path": "scripts/rungs_restriction_probe_2727.py",
                    "sha256": sha(os.path.abspath(__file__))},
        "p3_script_sha256": sha(P3),
        "art2720_sha256": sha(ART2720),
        "mp_dps_after_p3": str(mp.mp.dps),
    },
}
with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
    fh.write(json.dumps(payload, indent=2) + "\n")
log("wrote %s (verdict=%s)" % (os.path.basename(OUT), payload["verdict"]))