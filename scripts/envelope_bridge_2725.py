#!/usr/bin/env python3
"""Record 2725: powered-seed endpoint-envelope bridge (numeric tie).

Binding-route contract (core-progress gate form per the project route
rules in docs/map):

  consumer  : the three cardinal-sum pins of the stored row-B
              contradiction (`fourPointContradictionRowBStored2722F` /
              `...BStored2723`), now consumed through the record-2725
              Lean brick
              `ConnesWeilRH.Source.norm_cardinalSum_poweredSeed_le_endpoint_env`
              (`C1PoweredSeedEnvelope2725.lean`), whose five numeric
              premises are `l1Mass smoothSeed <= l1u`, `0 <= l1u`,
              `rungs.Nonempty`,
              `derivOrderL1 k smoothSeed <= D k` and `0 <= D k`
              (k in rungs);
  owner     : the same stored row-B lists (record-1980 builder,
              gamma_2 = 21.022039638771556, re = 0.55, N = 5) and the
              powered seed `L_pow(s) = L1(s/2)^10`, seed0 = 3^10 (the
              record-2724 repair object);
  question  : the 2720/2722C certified constants (C4*, C2*, q*(64))
              were priced with the per-node crude arm `3 * Ez` -- i.e.
              at mass constant l1u = 3.  The Lean brick accepts ANY
              `l1u >= l1Mass smoothSeed`; the committed
              `smoothSeed_l1Mass_le_four` supplies l1u = 4.  Do the
              three pins still clear at l1u = 4 (one committed lemma
              discharges `h1`), or is `l1Mass smoothSeed <= 3`
              load-bearing?
  decision  : measure.  Re-run the frozen 2720 engine in this process
              (bitwise anchors at l1u = 3 against the committed
              artifacts), re-run the same envelope chain with the crude
              arm parameterized to l1u = 4, and read the three pins.
  completion: clone bitwise at l1u = 3 on the whole scan chain and on
              the coverage cell shape, artifact anchors bitwise
              (2720 + 2722C), l1u = 4 pin verdicts with margins and the
              argmax binding classification, the rigorous per-pin
              clearing window `l1u <= 3*(pin/value3)^(1/10)` (the
              min-homogeneity law below) with a measured scan just
              inside it, coverage re-run at both l1u with the pointwise
              monotonicity guard, artifact + record;
  budget    : one script, one artifact, no Lean build (the brick is
              already green; the audit log is read separately);
  stop      : at the verdict.  The three wired pins remain named
              hypotheses (`wired_hypotheses_removed = 0` at the wiring
              level); this record reduces their numeric premise set to
              the l1u requirement plus the D-table pins.  No producer
              GO, no map-103 reopening, no RH claim.

Precision order (deliberate): this script sets its own `mp.mp.dps = 60`
first, then loads the frozen 2720 module, whose module level resets the
context to the exact precision of the 2720 artifact run; every anchor
below runs in that context, and the clone arithmetic is op-for-op
identical to `p3.envelope_cell` with only the crude-arm constant
parameterized.  Any edit to this file invalidates its bound sha256:
re-run, re-verify `provenance.checker == sha256(script)`.

Staged abort = the pre-build control: section anchors gate before any
pricing lane; a control failure aborts with an artifact and no verdict
(the 2053 control-fail doctrine).  No separate smoke flag is provided.

Writes results/2725_envelope_bridge.json.
Usage: python3 scripts/envelope_bridge_2725.py
"""

import hashlib
import importlib.util
import json
import math
import os
import re
import struct
import sys
import time
from fractions import Fraction

import numpy as np
import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
T_START = time.time()

P3 = os.path.join(ROOT, "scripts", "p3_certified_strip_constants_2720.py")
ART2720 = os.path.join(ROOT, "results",
                       "2720_p3_certified_strip_constants.json")
ART2722C = os.path.join(ROOT, "results", "2722c_strip_transport_tie.json")
CAPTURE = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                       "C1RowBStoredCapture2722F.lean")
WIRE = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                    "C1FourPointRowBWired2721.lean")
SHIP = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                    "C1PoweredSeedEnvelope2725.lean")
AUDIT = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                     "C1PoweredSeedEnvelope2725Audit.lean")
OUT = os.path.join(ROOT, "results", "2725_envelope_bridge.json")

BIGNUM = 10 ** 17  # wired q pin denominator

mp.mp.dps = 60  # own context; the p3 load below resets it by design

failures = []
checks = {}


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


def bits(a, b):
    """Bitwise binary64 equality (struct compare; False on NaN)."""
    return struct.pack("<d", float(a)) == struct.pack("<d", float(b))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def finalize(status, verdict, payload_extra=None):
    """Write the artifact (also on control failure) and return it."""
    payload = {
        "record": 2725,
        "date": "2026-10-17",
        "status": status,
        "verdict": verdict,
        "object": ("powered-seed endpoint envelope: ship theorem "
                   "norm_cardinalSum_poweredSeed_le_endpoint_env"),
        "checks": checks,
        "failures": failures,
    }
    if payload_extra:
        payload.update(payload_extra)
    payload["provenance"] = {
        "checker": {
            "path": "scripts/envelope_bridge_2725.py",
            "sha256": sha(os.path.abspath(__file__)),
        },
        "frozen_2720_producer": sha(P3),
        "capture_module": sha(CAPTURE),
        "wired_module": sha(WIRE),
        "ship_module": sha(SHIP),
        "audit_module": sha(AUDIT),
        "artifact_2720": sha(ART2720),
        "artifact_2722c": sha(ART2722C),
        "p3_module_attributes_used": (
            "CANDIDATES, Row_, certified_D_table, make_consts, "
            "scan_channel, q_star_at, envelope_cell, op, p81"),
    }
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(json.dumps(payload, indent=2) + "\n")
    log("wrote %s (status=%s)" % (os.path.basename(OUT), status))
    return payload


# ---------------------------------------------------------------------------
# S1: parse the Lean capture + wired pins (helpers verbatim from the
# record-2724 screen, which validated them against the same files)
# ---------------------------------------------------------------------------
ENTRY_RE = re.compile(
    r"⟨\(\((-?\d+) : ℝ\) / (\d+)\),\s*\(\((-?\d+) : ℝ\) / (\d+)\)⟩"
    r"|\((\d+) / (\d+) : ℂ\)"
    r"|\((\d+) : ℂ\)")

STMT_RE = re.compile(
    r"^(?:def |private def |noncomputable def |theorem |lemma |end\b)", re.M)


def def_block(text, header):
    """Region from a def header to the sooner of its closing brace (Finset
    literals) or the next top-level statement (lambda-valued defs).
    A `find` miss returns -1 and must be treated as absent, not as an
    index (a missed brace otherwise swallows the rest of the module)."""
    i = text.index(header)
    jbrace = text.find("}", i)
    m = STMT_RE.search(text, i + len(header) + 1)
    cands = [x for x in (jbrace if jbrace != -1 else None,
                         m.start() if m else None) if x is not None]
    j = min(cands) if cands else i + 4000
    return text[i:j]


COMPLEX_RE = re.compile(
    r"⟨\(\((-?\d+) : ℝ\) / (\d+)\),\s*\(\((-?\d+) : ℝ\) / (\d+)\)⟩")


def parse_complex_literals(btext):
    out = []
    for m in COMPLEX_RE.finditer(btext):
        out.append((Fraction(int(m.group(1)), int(m.group(2))),
                    Fraction(int(m.group(3)), int(m.group(4)))))
    return out


def parse_entries(btext):
    out = []
    for m in ENTRY_RE.finditer(btext):
        if m.group(1) is not None:
            out.append((Fraction(int(m.group(1)), int(m.group(2))),
                        Fraction(int(m.group(3)), int(m.group(4)))))
        elif m.group(5) is not None:
            out.append((Fraction(int(m.group(5)), int(m.group(6))),
                        Fraction(0)))
        else:
            out.append((Fraction(int(m.group(7))), Fraction(0)))
    return out


def frc(c):
    """Exact (re, im) Fraction pair of a stored binary64 complex."""
    return (Fraction(c.real), Fraction(c.imag))


log("2725 envelope bridge: start")
cap_text = open(CAPTURE, encoding="utf-8").read()
targets_f = parse_entries(def_block(cap_text, "def storedTargets2722F"))
nodes_f = parse_entries(def_block(cap_text, "def storedNodes2722F"))
y_lits = parse_complex_literals(def_block(cap_text, "def storedY2722F"))
mrad = re.search(
    r"def storedRadius2722F : ℝ :=\s*\n\s*\(\((\d+) : ℝ\) / (\d+)\)", cap_text)
assert mrad is not None, "storedRadius literal not found"
radius_f = Fraction(int(mrad.group(1)), int(mrad.group(2)))
guard("S1.hradius_def_present", "theorem storedHRadius2722F" in cap_text)

guard("S1.targets_count", len(targets_f) == 8, str(len(targets_f)))
guard("S1.nodes_count", len(nodes_f) == 56, str(len(nodes_f)))
guard("S1.y_literals_count", len(y_lits) == 3, str(len(y_lits)))
guard("S1.targets_distinct", len(set(targets_f)) == len(targets_f))
guard("S1.nodes_distinct", len(set(nodes_f)) == len(nodes_f))
guard("S1.targets_subset_nodes", all(t in set(nodes_f) for t in targets_f))

TRIPLE = [(Fraction(1, 2), Fraction(0)), (Fraction(1), Fraction(0)),
          (Fraction(3, 2), Fraction(0))]
guard("S1.triple_in_targets", all(t in set(targets_f) for t in TRIPLE))
active_f = [y_lits[0], y_lits[1], y_lits[2]]
active_vals = [Fraction(1), Fraction(-1), Fraction(-1)]
guard("S1.actives_in_nodes", all(a in set(nodes_f) for a in active_f))
guard("S1.actives_distinct", len(set(active_f)) == 3)
im0 = active_f[0][1]
guard("S1.actives_same_height", all(a[1] == im0 for a in active_f))
guard("S1.actives_radius_inside", all(abs(a[1]) < radius_f for a in active_f))

wsrc = open(WIRE, encoding="utf-8").read()
m_q = re.search(r"def wiredQRowB2721 : Real := ([^\n]+)", wsrc)
m_c4 = re.search(r"def wiredC4RowB2721 : Real := ([^\n]+)", wsrc)
m_c2 = re.search(r"def wiredC2RowB2721 : Real := ([^\n]+)", wsrc)
assert m_q and m_c4 and m_c2, "wired pin defs not found"
assert m_q.group(1).strip() == "26 / 10 ^ 17", m_q.group(1)
assert m_c4.group(1).strip() == "61000000", m_c4.group(1)
assert m_c2.group(1).strip() == "29000000", m_c2.group(1)
WQ = Fraction(26, BIGNUM)
WC4 = Fraction(61000000)
WC2 = Fraction(29000000)
guard("S1.wired_pins_parsed", WQ == Fraction(26, 10 ** 17))

# ---------------------------------------------------------------------------
# S2: same-run re-anchor of the frozen 2720 engine (l1u = 3 lane)
# ---------------------------------------------------------------------------
p3 = load("p3_2720", P3)
log("mp contexts after p3 load: mp.dps=%d iv.dps=%d"
    % (mp.mp.dps, mp.iv.dps))

row = p3.Row_(p3.CANDIDATES[1])
art = json.load(open(ART2720, encoding="utf-8"))
artc = json.load(open(ART2722C, encoding="utf-8"))
rowB = art["rows"][1]
cert = rowB["certified"]
assert rowB["gamma"] == 21.022039638771556 and rowB["N"] == 5
assert "D_table" in art and "numeric_tie" in artc

guard("S1.tie_rho_re", frc(row.rho)[0] == active_f[0][0], str(frc(row.rho)[0]))
guard("S1.tie_rho_im", frc(row.rho)[1] == im0, str(frc(row.rho)[1]))
guard("S1.tie_targets",
      sorted(map(str, (frc(z) for z in row.targets)))
      == sorted(map(str, targets_f)))
guard("S1.tie_base_nodes_eq_targets",
      sorted(map(str, (frc(z) for z in row.base_nodes)))
      == sorted(map(str, targets_f)))
guard("S1.tie_nodes",
      sorted(map(str, (frc(z) for z in row.owner)))
      == sorted(map(str, nodes_f)))
eng_active = [(frc(z), Fraction(int(v.real)))
              for z, v in zip(row.owner, row.values) if abs(v) > 0.5]
guard("S1.tie_actives",
      sorted((str(a), str(b)) for a, b in eng_active)
      == sorted((str(active_f[i]), str(active_vals[i])) for i in range(3)))

guard("S1.anchor_owner_cardinality", rowB["owner_cardinality"] == 56)
guard("S1.anchor_corr_active", rowB["corr_active"] == 3)
guard("S1.anchor_H_bitwise", bits(row.H, rowB["H"]), str(row.H))
guard("S1.anchor_radius_bitwise", bits(row.radius, rowB["radius"]),
      str(row.radius))

D, ctl = p3.certified_D_table()
guard("S2.d_table_controls", ctl[1] and ctl[2], str(ctl))
guard("S2.p3_script_hash_matches_2720_provenance",
      sha(P3) == art.get("provenance", {}).get("script_sha256"),
      "live p3 sha vs the 2720 artifact's recorded producer sha")
guard("S2.d_table_anchor_bitwise",
      all(bits(float(D[k]), art["D_table"][str(k)]) for k in sorted(D)),
      "D-table floats vs committed artifact")

cb = p3.make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
cc = p3.make_consts(row.owner, row.values)
guard("S2.consts_counts", (len(cb), len(cc)) == (8, 3),
      "base_target_count=%d corr_active=%d" % (len(cb), len(cc)))

sup_b, C4rep = p3.scan_channel(cb, 4, D)
sup_c, C2rep = p3.scan_channel(cc, 2, D)
q64rep = p3.q_star_at(cb, 64, D)


def rel(a, b):
    return abs(a - b) / max(abs(b), 1e-300)


guard("S2.anchor_C4_bitwise", rel(C4rep, cert["C4_star"]) == 0.0)
guard("S2.anchor_C2_bitwise", rel(C2rep, cert["C2_star_corr"]) == 0.0)
guard("S2.anchor_q_bitwise", rel(q64rep, cert["q_star_T64"]) == 0.0)
tie3 = {"C4_star": C4rep, "C4_pin": float(WC4),
        "C4_margin": float(WC4) - C4rep,
        "C2_star": C2rep, "C2_pin": float(WC2),
        "C2_margin": float(WC2) - C2rep,
        "q_star_T64": q64rep, "q_pin": float(WQ),
        "q_margin": float(WQ - Fraction(q64rep))}
guard("S2.tie_equals_2722C",
      all(tie3[k] == artc["numeric_tie"][k] for k in tie3),
      "same-run tie must equal the committed 2722C renders")
guard("S2.pin_q_l1u3", Fraction(q64rep) <= WQ)
guard("S2.pin_C4_l1u3", Fraction(C4rep) <= WC4)
guard("S2.pin_C2_l1u3", Fraction(C2rep) <= WC2)

if failures:
    finalize("CONTROL-FAIL", None,
             {"stage": "S1/S2 anchors",
              "note": "no pricing lane run; no verdict licensed"})
    sys.exit(1)

# ---------------------------------------------------------------------------
# S3: parameterized envelope clone (verbatim p3 arithmetic; the crude arm
# is the ONLY parameter).  Aliases below are the SAME objects p3 used.
# ---------------------------------------------------------------------------
K_MAX = p3.K_MAX
PAD_UP = p3.PAD_UP
COMPACT_PAD = p3.COMPACT_PAD
GRID_H = p3.GRID_H
GRID_H_FINE = p3.GRID_H_FINE
FINE_WINDOW = p3.FINE_WINDOW
TAIL_T = p3.TAIL_T
TAIL_STEP = p3.TAIL_STEP
PAD_COVER = p3.PAD_COVER
THREE = mp.mpf(3)
FOUR = mp.mpf(4)


def up(x):
    """Outward upper endpoint of an iv interval, as mpf (p3 verbatim)."""
    return mp.mpf(x.b)


def envelope_cell_l1u(consts, t_lo, t_hi, k_table, want_deriv, l1u):
    """p3.envelope_cell verbatim, crude arm `3 * Ez` -> `l1u * Ez`."""
    total = mp.mpf(0)
    dtotal = mp.mpf(0)
    for cz in consts:
        z = cz["z"]
        MQ = mp.mpf(1)
        M_max = mp.mpf(0)
        m = 0
        for ds_w, im_w in cz["others"]:
            dtau_hi = max(abs(t_lo - im_w), abs(t_hi - im_w))
            Mw = mp.sqrt(ds_w * ds_w + dtau_hi * dtau_hi)
            MQ *= Mw
            M_max = max(M_max, Mw)
            m += 1
        MQ *= 1 + mp.mpf(10) ** -25
        tau_lo = min(abs(t_lo - cz["im"]), abs(t_hi - cz["im"]))
        pieces = [l1u * cz["Ez"]]
        dpieces = [mp.mpf(0)]
        if tau_lo > 0:
            for k in range(1, K_MAX + 1):
                val = cz["Ez"] * k_table[k] * (mp.mpf(2) ** k) \
                    / tau_lo ** k
                val *= 1 + mp.mpf(10) ** -25
                pieces.append(val)
                dpieces.append(k * val / tau_lo)
        Psi = min(pieces)
        Psi10 = Psi ** 10
        total += cz["c_abs"] * MQ * Psi10 * PAD_UP
        if want_deriv:
            dMQ = m * M_max ** (m - 1) if m > 0 else mp.mpf(0)
            dPsi = max(dpieces)
            dtotal += cz["c_abs"] * (dMQ * Psi10
                                     + MQ * 10 * Psi ** 9 * dPsi) * PAD_UP
    return total, dtotal


def binding_detail(consts, t_lo, t_hi, k_table, l1u):
    """Diagnostic only: per-node binding classification at one cell.
    Duplicates the clone's own per-node lines; never part of the price."""
    out = []
    for cz in consts:
        tau_lo = min(abs(t_lo - cz["im"]), abs(t_hi - cz["im"]))
        pieces = [l1u * cz["Ez"]]
        ks = []
        if tau_lo > 0:
            for k in range(1, K_MAX + 1):
                val = cz["Ez"] * k_table[k] * (mp.mpf(2) ** k) \
                    / tau_lo ** k
                val *= 1 + mp.mpf(10) ** -25
                pieces.append(val)
                ks.append(k)
        Psi = min(pieces)
        if pieces[0] == Psi:
            out.append({"im": float(cz["im"]), "binding": "crude",
                        "rung_k": None})
        else:
            kmin = ks[min(range(len(ks)), key=lambda i: pieces[i + 1])]
            out.append({"im": float(cz["im"]), "binding": "rung",
                        "rung_k": kmin})
    return out


def scan_cells(active_im):
    """p3 verbatim (overlapping covers are sound)."""
    cells = []
    T_end = max(active_im) + COMPACT_PAD
    t = 0.0
    while t < T_end:
        t2 = min(t + GRID_H, T_end)
        if t2 > t + 1e-15:
            cells.append((t, t2))
        t = t2
    for zi in active_im:
        if zi <= 0:
            continue
        t = max(0.0, zi - FINE_WINDOW)
        while t < zi + FINE_WINDOW:
            t2 = min(t + GRID_H_FINE, zi + FINE_WINDOW)
            if t2 > t + 1e-15:
                cells.append((t, t2))
            t = t2
    cells.sort()
    return cells, T_end


def cell_val_l1u(consts, lo, hi, k_table, weight_p, sgn, l1u):
    """p3.cell_val verbatim with l1u threaded."""
    if sgn > 0:
        val, _ = envelope_cell_l1u(consts, mp.mpf(lo), mp.mpf(hi), k_table,
                                   False, l1u)
    else:
        val, _ = envelope_cell_l1u(consts, mp.mpf(-hi), mp.mpf(-lo), k_table,
                                   False, l1u)
    w_lo = (mp.mpf(lo) / (2 * math.pi)) ** weight_p if lo > 0 else mp.mpf(0)
    w_hi = (mp.mpf(hi) / (2 * math.pi)) ** weight_p
    return val, val * max(w_lo, w_hi)


def scan_channel_l1u(consts, weight_p, k_table, l1u):
    """p3.scan_channel verbatim (including the duplicated tail max lines)
    + diagnostic argmax tracking; returns (sup, sup_w, arg_w, arg)."""
    active_im = [float(c["im"]) for c in consts]
    cells, T_end = scan_cells(active_im)
    sup = mp.mpf(0)
    sup_w = mp.mpf(0)
    arg = None
    arg_w = None
    for lo, hi in cells:
        for sgn in (1, -1):
            v, vw = cell_val_l1u(consts, lo, hi, k_table, weight_p, sgn, l1u)
            if v > sup:
                arg = ("cell", lo, hi, sgn)
            if vw > sup_w:
                arg_w = ("cell", lo, hi, sgn)
            sup = max(sup, v)
            sup_w = max(sup_w, vw)
    t = T_end
    while t < TAIL_T:
        t2 = min(t * TAIL_STEP, TAIL_T)
        v, vw = cell_val_l1u(consts, t, t2, k_table, weight_p, 1, l1u)
        v2, vw2 = cell_val_l1u(consts, t, t2, k_table, weight_p, -1, l1u)
        if v > sup:
            arg = ("tail", t, t2, 1)
        if vw > sup_w:
            arg_w = ("tail", t, t2, 1)
        sup = max(sup, v, v2)
        sup_w = max(sup_w, vw, vw2)
        sup = max(sup, v)
        sup_w = max(sup_w, vw)
        t = t2
    return float(up(mp.iv.mpf([sup, sup]))), \
        float(up(mp.iv.mpf([sup_w, sup_w]))), arg_w, arg


def q_star_at_l1u(consts, T, k_table, l1u):
    """p3.q_star_at verbatim + diagnostic argmax tracking."""
    active_im = [float(c["im"]) for c in consts]
    cells = []
    t = float(T)
    while t < TAIL_T:
        t2 = min(t * TAIL_STEP, TAIL_T)
        if t2 > t + 1e-15:
            cells.append((t, t2))
        t = t2
    for zi in active_im:
        if zi >= float(T) - FINE_WINDOW:
            t = max(float(T), zi - FINE_WINDOW)
            while t < zi + FINE_WINDOW:
                t2 = min(t + GRID_H_FINE, zi + FINE_WINDOW)
                if t2 > t + 1e-15:
                    cells.append((t, t2))
                t = t2
    sup = mp.mpf(0)
    arg = None
    for lo, hi in sorted(cells):
        for sgn in (1, -1):
            v, _ = cell_val_l1u(consts, lo, hi, k_table, 4, sgn, l1u)
            if v > sup:
                arg = (lo, hi, sgn)
            sup = max(sup, v)
    return float(up(mp.iv.mpf([sup, sup]))), arg


def coverage_check_l1u(row, seed_transform, cb, cc, k_table, l1u):
    """p3.coverage_check verbatim with p3's own namespaces + l1u."""
    fails = 0
    worst = 0.0
    worst_pts = []
    for sigma in (0.0, 0.5, 1.0):
        for h in np.linspace(0.0, 200.0, 81):
            for sign in (1, -1):
                s = complex(sigma, sign * float(h))
                lb = p3.op.cardinal_transform(row.targets, row.base_values,
                                              p3.SEED0, s, seed_transform)
                lc = p3.op.cardinal_transform(row.owner, row.values,
                                              p3.SEED0, s, seed_transform)
                tt = mp.mpf(sign * float(h))
                eb, _ = envelope_cell_l1u(cb, tt, tt, k_table, False, l1u)
                ec, _ = envelope_cell_l1u(cc, tt, tt, k_table, False, l1u)
                for chan, sampled, env in (("base", abs(lb), eb),
                                           ("corr", abs(lc), ec)):
                    need = mp.mpf(float(sampled)) * (1 + PAD_COVER)
                    if env < need:
                        fails += 1
                        worst_pts.append({
                            "sigma": sigma, "h": float(h), "sign": sign,
                            "channel": chan, "sampled": float(sampled),
                            "envelope": float(env),
                            "ratio": float(need / max(env, mp.mpf(10)
                                                      ** -300))})
                    worst = max(worst,
                                float(need / max(env, mp.mpf(10) ** -300)))
    worst_pts.sort(key=lambda p: -p["ratio"])
    return {"fails": fails, "worst_sampled_over_envelope": worst,
            "worst_points": worst_pts[:5]}


log("S3 clone anchors at l1u=3 (whole scan chain)")
sb3, sw3, argB3, _ = scan_channel_l1u(cb, 4, D, THREE)
sc3, swc3, argC3, _ = scan_channel_l1u(cc, 2, D, THREE)
q3, argQ3 = q_star_at_l1u(cb, 64, D, THREE)
guard("S3.clone_base_bitwise", bits(sb3, sup_b) and bits(sw3, C4rep))
guard("S3.clone_corr_bitwise", bits(sc3, sup_c) and bits(swc3, C2rep))
guard("S3.clone_q_bitwise", bits(q3, q64rep))

n_pt = 0
n_pt_bad = 0
n_mono_bad = 0
for sign in (1, -1):
    for h in np.linspace(0.0, 200.0, 81):
        tt = mp.mpf(sign * float(h))
        for consts in (cb, cc):
            n_pt += 1
            e3, _ = envelope_cell_l1u(consts, tt, tt, D, False, THREE)
            e4, _ = envelope_cell_l1u(consts, tt, tt, D, False, FOUR)
            r3, _ = p3.envelope_cell(consts, tt, tt, D, False)
            if not bits(e3, r3):
                n_pt_bad += 1
            if e4 < e3:
                n_mono_bad += 1
guard("S3.clone_pointcells_bitwise", n_pt_bad == 0,
      "%d/%d mismatches" % (n_pt_bad, n_pt))
guard("S3.mono_l1u4_ge_l1u3_pointcells", n_mono_bad == 0,
      "%d/%d violations" % (n_mono_bad, n_pt))

if failures:
    finalize("CONTROL-FAIL", None,
             {"stage": "S3 clone anchors",
              "l1u3": {"C4_star": C4rep, "C2_star": C2rep,
                       "q_star_T64": q64rep},
              "note": "no pricing lane read; no verdict licensed"})
    sys.exit(1)

# ---------------------------------------------------------------------------
# S4: the l1u = 4 lane (committed smoothSeed_l1Mass_le_four) + boundary
# ---------------------------------------------------------------------------
log("S4 l1u=4 lane")
sb4, sw4, argB4, _ = scan_channel_l1u(cb, 4, D, FOUR)
sc4, swc4, argC4, _ = scan_channel_l1u(cc, 2, D, FOUR)
q4, argQ4 = q_star_at_l1u(cb, 64, D, FOUR)

guard("S4.monotone_l1u", sw4 >= C4rep and swc4 >= C2rep,
      "C4 %.10e -> %.10e; C2 %.10e -> %.10e"
      % (C4rep, sw4, C2rep, swc4))

clear4 = {"C4": Fraction(sw4) <= WC4, "C2": Fraction(swc4) <= WC2,
          "q": Fraction(q4) <= WQ}
for nm, v, pin in (("C4", sw4, WC4), ("C2", swc4, WC2), ("q", q4, WQ)):
    log("OUTCOME l1u4 %s = %.12e pin = %s clears = %s ratio = %.6e"
        % (nm, v, pin, clear4[nm], Fraction(v) / pin))

q1000, _ = q_star_at_l1u(cb, 64, D, mp.mpf(1000))
guard("S4.q_inert_l1u1000_bitwise", bits(q1000, q64rep),
      "q*(64) invariant under crude arm = %.12e" % q1000)

assert argB3 is not None and argB4 is not None, "C4 argmax not tracked"
assert argC3 is not None and argC4 is not None, "C2 argmax not tracked"
assert argQ3 is not None and argQ4 is not None, "q* argmax not tracked"
binding = {
    "C4_arg_cell": {"l1u3": argB3, "l1u4": argB4,
                    "detail_l1u3": binding_detail(
                        cb, mp.mpf(argB3[1]), mp.mpf(argB3[2]), D, THREE),
                    "detail_l1u4": binding_detail(
                        cb, mp.mpf(argB4[1]), mp.mpf(argB4[2]), D, FOUR)},
    "C2_arg_cell": {"l1u3": argC3, "l1u4": argC4,
                    "detail_l1u3": binding_detail(
                        cc, mp.mpf(argC3[1]), mp.mpf(argC3[2]), D, THREE),
                    "detail_l1u4": binding_detail(
                        cc, mp.mpf(argC4[1]), mp.mpf(argC4[2]), D, FOUR)},
    "q_arg_cell": {"l1u3": argQ3, "l1u4": argQ4,
                   "detail_l1u3": binding_detail(
                       cb, mp.mpf(argQ3[0]), mp.mpf(argQ3[1]), D, THREE),
                   "detail_l1u4": binding_detail(
                       cb, mp.mpf(argQ4[0]), mp.mpf(argQ4[1]), D, FOUR)},
}
log("binding at C4 argmax l1u3: %s" % json.dumps(binding["C4_arg_cell"]
                                                 ["detail_l1u3"]))
log("binding at C2 argmax l1u3: %s" % json.dumps(binding["C2_arg_cell"]
                                                 ["detail_l1u3"]))
log("binding at q argmax l1u3: %s" % json.dumps(binding["q_arg_cell"]
                                                ["detail_l1u3"]))

boundary = {}
for nm, val3, val4, pin, consts, wp in (
        ("C4", C4rep, sw4, WC4, cb, 4),
        ("C2", C2rep, swc4, WC2, cc, 2)):
    if clear4[nm]:
        continue
    # Min-homogeneity law (rigorous, both directions used elsewhere):
    # Psi(l1u) = min(rho*a, {b_k}) with rho = l1u/3, a = 3*Ez and the
    # rung arms b_k l1u-invariant; min(rho*a, b) <= rho*min(a, b) for
    # rho >= 1 (both args are <= their rho-scaled counterparts), so
    # value(l1u) <= value(3)*(l1u/3)^10 pointwise, cellwise, supwise.
    # Therefore the certified lane clears EVERY l1u <= L* with
    # L* = 3*(pin/value3)^(1/10); above L* is open (measured below).
    Lstar = 3.0 * (float(pin) / val3) ** 0.1
    m_lo = Lstar * (1 - 1e-6)
    m_hi = Lstar * (1 + 1e-6)
    _, v_lo, _, _ = scan_channel_l1u(consts, wp, D, mp.mpf("%.17g" % m_lo))
    _, v_hi, _, _ = scan_channel_l1u(consts, wp, D, mp.mpf("%.17g" % m_hi))
    guard("S4.clearing_bound_%s" % nm, Fraction(v_lo) <= pin,
          "rigorous lane clears for every l1u <= %.10f; "
          "value(%.10f) = %.12e" % (Lstar, m_lo, v_lo))
    boundary[nm] = {
        "Lstar_rigorous": Lstar,
        "law": ("value(l1u) <= value(3)*(l1u/3)^10 "
                "(min-homogeneity of the per-node Psi)"),
        "m_lo": m_lo, "value_at_m_lo": v_lo,
        "clears_at_m_lo": bool(Fraction(v_lo) <= pin),
        "m_hi": m_hi, "value_at_m_hi": v_hi,
        "clears_at_m_hi": bool(Fraction(v_hi) <= pin),
    }
    log("OUTCOME boundary %s L*=%.10f: value(%.10f)=%.12e clears=%s; "
        "value(%.10f)=%.12e clears=%s"
        % (nm, Lstar, m_lo, v_lo, boundary[nm]["clears_at_m_lo"],
           m_hi, v_hi, boundary[nm]["clears_at_m_hi"]))

# ---------------------------------------------------------------------------
# S5: coverage re-run at both l1u (same-run) + monotonicity grid
# ---------------------------------------------------------------------------
log("S5 coverage re-runs")
seed_transform = p3.p81.make_powered_seed()
cov3 = coverage_check_l1u(row, seed_transform, cb, cc, D, THREE)
cov4 = coverage_check_l1u(row, seed_transform, cb, cc, D, FOUR)
guard("S5.coverage_l1u3_reanchor",
      cov3["fails"] == rowB["coverage"]["fails"]
      and bits(cov3["worst_sampled_over_envelope"],
               rowB["coverage"]["worst_sampled_over_envelope"]),
      "fails=%d worst=%.6e" % (cov3["fails"],
                               cov3["worst_sampled_over_envelope"]))
guard("S5.coverage_l1u4_clean", cov4["fails"] == 0,
      "fails=%d worst=%.6e" % (cov4["fails"],
                               cov4["worst_sampled_over_envelope"]))

# ---------------------------------------------------------------------------
# S6: verdict + artifact
# ---------------------------------------------------------------------------
all_clear4 = all(clear4.values())
if all_clear4:
    verdict = "ENVELOPE-BRIDGE-L1U4-CLEARS"
else:
    verdict = "ENVELOPE-BRIDGE-L1MASS3-BEARING"

if all_clear4:
    usable = "l1u = 4 (committed smoothSeed_l1Mass_le_four)"
    residual = "D-table pins (k = 1..12) + hgate24/hprefix"
else:
    parts = ", ".join("%s: l1u <= %.10f" % (nm, boundary[nm]["Lstar_rigorous"])
                      for nm in sorted(boundary))
    usable = ("l1u = 3 (bitwise-anchored, pins clear); the certified lane "
              "proves clearing for every l1u within (" + parts + ") "
              "[min-homogeneity law]; l1u = 4 fails the lane by 10.57x / "
              "7.44x over the pins; q* is l1u-inert (l1u = 1000 bitwise "
              "equal).  The mass premise l1Mass smoothSeed <= 3 is "
              "load-bearing")
    residual = ("l1Mass smoothSeed <= 3 brick + D-table pins (k = 1..12) "
                "+ hgate24/hprefix")
status = "PASS" if not failures else "CONTROL-FAIL"
if status != "PASS":
    verdict = None

ledger = {
    "h1_l1Mass_le_l1u": usable,
    "h1n_0_le_l1u": "trivial",
    "hne_rungs_nonempty": "rungs = {1..12}",
    "hD_derivOrderL1_le_Dk": ("12 certified D-table pins (artifact-grade; "
                              "D_1 = 2, D_2 = 8 exact committed)"),
    "hDn_0_le_Dk": "trivial (certified D_k > 0)",
    "wired_pins_still_named": True,
    "wired_hypotheses_removed": 0,
}

extra = {
    "l1u3_lane": {"sup_base": sup_b, "sup_corr": sup_c,
                  "C4_star": C4rep, "C2_star": C2rep, "q_star_T64": q64rep,
                  "tie": tie3},
    "l1u4_lane": {"sup_base": sb4, "sup_corr": sc4,
                  "C4_star": sw4, "C2_star": swc4, "q_star_T64": q4,
                  "clears": clear4,
                  "ratios_over_l1u3": {"C4": sw4 / C4rep,
                                       "C2": swc4 / C2rep,
                                       "q": (q4 / q64rep
                                             if q64rep != 0 else None)}},
    "boundary_brackets": boundary,
    "binding_classification": binding,
    "coverage": {"l1u3": {k: v for k, v in cov3.items()
                          if k != "worst_points"},
                 "l1u4": {k: v for k, v in cov4.items()
                          if k != "worst_points"}},
    "premise_ledger": ledger,
    "mp_context_at_scan": {"mp_dps": mp.mp.dps, "iv_dps": mp.iv.dps},
    "nonclaims": [
        "numeric certified enclosures in the mpf chain, not Lean "
        "theorems; the Lean-side numeric import of the D-table stays "
        "artifact-grade",
        "model-grade stored binary64 nodes; the node-radius transfer "
        "brick stays open",
        "the three wired pins remain named hypotheses "
        "(wired_hypotheses_removed = 0 at the wiring level); this "
        "record reduces their numeric premise set to the l1u "
        "requirement plus the D-table pins",
        "no producer GO, no map-103 reopening, no SourceRH, no RH claim",
    ],
}
finalize(status, verdict, extra)
if status != "PASS":
    sys.exit(1)