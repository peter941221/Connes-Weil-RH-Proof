#!/usr/bin/env python3
"""Record 2727 companion probe: the D_4 margin of the wired q pin.

Decision it settles: how much slack the D-ladder brick at order 4 (the ONLY
open order after the rung-collapse probe, see
`scripts/rungs_restriction_probe_2727.py`) has against the wired pins.

Method: re-run the frozen 2720 engine on stored row B with rungs {1,2,3,4}
and D_4 := D_4 * (1 + eps) for a bracket of eps values; a same-run
full-table control must reproduce the committed artifact bitwise first.
Also measures the TRUE `derivOrderL1 k smoothSeed = 4 int_0^{1/2} |T^(k)|`
for k = 1..6 by high-precision quadrature (diagnostic grade: it sizes the
brick, it is not a certificate).

Writes results/2727_d4_margin.json.
Usage: python3 scripts/d4_margin_probe_2727.py
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
OUT = os.path.join(ROOT, "results", "2727_d4_margin.json")

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
    return struct.pack("<d", float(a)) == struct.pack("<d", float(b))


p3 = load("p3", P3)
art = json.load(open(ART2720, encoding="utf-8"))
rowB = art["rows"][1]
guard("S0.row_identity",
      rowB["gamma"] == 21.022039638771556 and rowB["N"] == 5,
      str((rowB["gamma"], rowB["N"])))
cert = rowB["certified"]

row = p3.Row_(p3.CANDIDATES[1])
D, _ctl = p3.certified_D_table()
cb = p3.make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
cc = p3.make_consts(row.owner, row.values)

# --- same-run control (full table, all 12 rungs) ---------------------------
_sb, C4_full = p3.scan_channel(cb, 4, D)
_sc, C2_full = p3.scan_channel(cc, 2, D)
q64_full = p3.q_star_at(cb, 64, D)
guard("S1.control_C4_bitwise", bits(C4_full, cert["C4_star"]))
guard("S1.control_C2_bitwise", bits(C2_full, cert["C2_star_corr"]))
guard("S1.control_q_bitwise", bits(q64_full, cert["q_star_T64"]))

if failures:
    payload = {"record": 2727, "status": "CONTROL-FAIL", "checks": checks,
               "failures": failures}
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(json.dumps(payload, indent=2) + "\n")
    log("CONTROL-FAIL")
    sys.exit(1)

# --- S2: true ladder values (diagnostic, mpmath quadrature) ----------------
# T(u) = 1/(1+exp(1/u - 1/(1-u))) on (0,1); smoothSeedRaw = T(x+2)T(2-x),
# derivOrderL1 k smoothSeed = 4 int_0^{1/2} |T^(k)| (mirror symmetry).
fT = lambda u: 1 / (1 + mp.e ** (1 / u - 1 / (1 - u)))
true_vals = {}
for k in (1, 2, 3, 4, 5, 6):
    g = lambda u, k=k: abs(mp.diff(fT, u, k))
    val = 4 * mp.quad(g, [0, mp.mpf(1) / 4096, mp.mpf(1) / 64,
                          mp.mpf(1) / 8, mp.mpf(1) / 4, mp.mpf(1) / 2])
    true_vals[k] = {
        "true": float(val),
        "D_table": float(D[k]),
        "ratio_D_over_true": float(D[k]) / float(val),
    }
    log("true k=%2d: %.9e  D_table %.9e  ratio %.6f"
        % (k, float(val), float(D[k]), float(D[k]) / float(val)))
guard("S2.integer_orders_exact",
      abs(true_vals[1]["true"] - 2) < 1e-9
      and abs(true_vals[2]["true"] - 8) < 1e-9)
guard("S2.order3_matches_lean_bracket",
      abs(true_vals[3]["true"] - 78.728338445) / 78.728338445 < 1e-5,
      "rel=%.2e" % (abs(true_vals[3]["true"] - 78.728338445)
                    / 78.728338445))

# --- S3: the D_4 slack bracket at rungs {1,2,3,4} --------------------------
PINS = {"C4": 61000000.0, "C2": 29000000.0, "q": 26e-17}
D4 = D[4]
eps_scan = {}
for eps in (0.0, 0.001, 0.002, 0.0025, 0.0029, 0.003, 0.004):
    Dr = {k: (D[k] if k <= 4 else mp.inf) for k in range(1, p3.K_MAX + 1)}
    Dr[4] = D4 * (1 + eps)
    _sb, C4 = p3.scan_channel(cb, 4, Dr)
    _sc, C2 = p3.scan_channel(cc, 2, Dr)
    q64 = p3.q_star_at(cb, 64, Dr)
    rec = {
        "C4_over_pin": C4 / PINS["C4"], "C4_clears": bool(C4 <= PINS["C4"]),
        "C2_over_pin": C2 / PINS["C2"], "C2_clears": bool(C2 <= PINS["C2"]),
        "q_over_pin": q64 / PINS["q"], "q_clears": bool(q64 <= PINS["q"]),
    }
    rec["all_clear"] = rec["C4_clears"] and rec["C2_clears"] \
        and rec["q_clears"]
    eps_scan["%.4f" % eps] = rec
    log("eps=%.4f: C4 %.8f %s | C2 %.8f %s | q %.8f %s" % (
        eps, rec["C4_over_pin"], rec["C4_clears"], rec["C2_over_pin"],
        rec["C2_clears"], rec["q_over_pin"], rec["q_clears"]))

clear_eps = [float(k) for k, v in eps_scan.items() if v["all_clear"]]
fail_eps = [float(k) for k, v in eps_scan.items() if not v["all_clear"]]
lo = max(clear_eps) if clear_eps else None
hi = min(fail_eps) if fail_eps else None
guard("S3.bracket_nonempty", lo is not None and hi is not None
      and lo < hi, "lo=%s hi=%s" % (lo, hi))
guard("S3.q_is_the_binding_channel",
      all(v["C4_clears"] and v["C2_clears"] for v in eps_scan.values()),
      "C4/C2 insensitive in the scanned range")

payload = {
    "record": 2727,
    "date": "2026-10-17",
    "status": "PROBE-FAIL" if failures else "PROBE-OK",
    "verdict": ("PROBE-FAIL" if failures else
                "D4-SLACK-BRACKET-[%s, %s]" % (lo, hi)),
    "object": ("stored row B three wired pins at rungs {1,2,3,4} with "
               "D_4 scaled by (1+eps); true derivOrderL1 k smoothSeed "
               "values k = 1..6 (diagnostic quadrature)"),
    "pins": PINS,
    "D4_table": float(D4),
    "true_vals": true_vals,
    "eps_scan": eps_scan,
    "slack_bracket": {"all_clear_at_or_below": lo,
                      "fails_at_or_above": hi},
    "checks": checks,
    "failures": failures,
    "nonclaims": [
        "engine-grade measurement + diagnostic quadrature; no Lean claim",
        "the true values are quadrature-grade (mp dps 60), not certificates",
        "no producer GO, no RH claim",
    ],
    "provenance": {
        "checker": {"path": "scripts/d4_margin_probe_2727.py",
                    "sha256": sha(os.path.abspath(__file__))},
        "p3_script_sha256": sha(P3),
        "art2720_sha256": sha(ART2720),
        "mp_dps_after_p3": str(mp.mp.dps),
    },
}
with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
    fh.write(json.dumps(payload, indent=2) + "\n")
log("wrote %s (verdict=%s)" % (os.path.basename(OUT), payload["verdict"]))
sys.exit(1 if failures else 0)
