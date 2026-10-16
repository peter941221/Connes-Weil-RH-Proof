#!/usr/bin/env python3
"""Record 2717 (G1 swing 2a): P5 n=3 probe -- channel flip-budget ledger and
two-grid honest joint for the stored map-103 gate rows.

Paper arithmetic on stored artifacts only (record-2716 precedent).  The
probe question: do the n=3 gate-branch signs at the two P4-admissible
owners -- (gamma_1, N=4, n=3) and (gamma_2, N=5, n=3) -- carry margins
that a %-grade certified enclosure can discharge?

Everything computed here is recovered from results/2032_gate_row_search.json
(C, b, D, det, lambda AND the archimedean integrals arch[0..2] per grid),
results/2033_gate_tail_pairing.json (decay constants, A0, H), and the
record-2716 artifact (A_n anchors).  No new measurement.

Channels (record-2032 gate_row):
    C = arch[0] + pr[0],  b = arch[1] + pr[1],  D = arch[2] + pr[2],
    pr[i] = trapezoid(kp * f_i),  arch[i] = trapezoid(sig * f_i),
    f = (W, P*W, P^2*W),  det = C*D - b*b.
The stored artifact carries arch[i] and the sums, so pr[i] = sum - arch[i]
exactly (rational subtraction of stored binary64 values).

Flip budgets (exact worst-case boxes; mpmath dps 30):
  eps_C     -- channel factor-eps box [x(1-eps), x(1+eps)] on (arch0, pr0):
               sign(C) certified for every eps < |C| / (|arch0| + |pr0|).
  eps_Delta -- factor box on (C, D, b): for C*D > 0 the sign of
               det = C*D - b^2 is sign(sqrt(C*D) - |b|), and worst-case
               factor boxes flip it only at
               eps = |sqrt(C*D) - |b|| / (sqrt(C*D) + |b|).
               For C*D <= 0, det <= 0 unconditionally (budget unbounded).
  eps_unif  -- ONE channel box certifying BOTH signs at once:
               |dC| <= eps S0, |dD| <= eps S2, |db| <= eps S1 with
               S_i = |arch_i| + |pr_i| gives
               |d(det)| <= eps (|D| S0 + |C| S2 + 2 |b| S1), so
               eps_unif = min(eps_C, |det| / (|D| S0 + |C| S2 + 2|b| S1)).

Anchors (in-run):
  a1  the 2033 stored rows are BITWISE the 2032 dxi0.02 rows (C,b,det,lambda)
  a2  stored lambda == float(b/C) bitwise on every stored gate entry
  a3  the 2716 A_n fields (both geometries) are reproduced EXACTLY from the
      committed constants (mpmath deterministic, same inputs)
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from mpmath import mpf

import g1_joint_acceptance_repricing_2716 as r16

mp.mp.dps = 30

ROOT = Path(__file__).resolve().parents[1]
SRC32 = ROOT / "results/2032_gate_row_search.json"
SRC33 = ROOT / "results/2033_gate_tail_pairing.json"
SRC16 = ROOT / "results/2716_g1_joint_acceptance_repricing.json"

Cspec = mp.mpf("128.65")
M_FLOOR = mp.mpf(1)
TWO_PI_12 = (2 * mp.pi) ** 12
SENS_32 = mpf(3) / 2
D_2710 = mpf(169) / 16              # record-2710 geometry (K^4 = d)

CANDIDATES = [(14.134725141734693, 4), (21.022039638771556, 5)]


def f2m(x: float):
    """Exact binary64 capture -> 30-dps."""
    fr = Fraction(x)
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def channels(gate_entry):
    """Recover the six channels from the stored sums and arch parts."""
    a0, a1, a2 = gate_entry["arch"]
    p0 = gate_entry["C"] - a0
    p1 = gate_entry["b"] - a1
    p2 = gate_entry["D"] - a2
    return (a0, a1, a2), (p0, p1, p2)


def budgets(entry):
    """Exact flip budgets from the stored floats of one gate entry."""
    (a0, a1, a2), (p0, p1, p2) = channels(entry)
    C, b, D = f2m(entry["C"]), f2m(entry["b"]), f2m(entry["D"])
    det = C * D - b * b

    s0 = abs(f2m(a0)) + abs(f2m(p0))
    s1 = abs(f2m(a1)) + abs(f2m(p1))
    s2 = abs(f2m(a2)) + abs(f2m(p2))

    eps_c = abs(C) / s0

    cd = C * D
    if cd > 0:
        eps_delta = abs(mp.sqrt(cd) - abs(b)) / (mp.sqrt(cd) + abs(b))
    else:
        eps_delta = None          # det <= 0 unconditionally

    denom = abs(D) * s0 + abs(C) * s2 + 2 * abs(b) * s1
    eps_unif = min(eps_c, abs(det) / denom)
    return {
        "eps_C": float(eps_c),
        "eps_Delta": (float(eps_delta) if eps_delta is not None else None),
        "eps_unified": float(eps_unif),
        "cancel_sums": {"S0": float(s0), "S1": float(s1), "S2": float(s2)},
    }


def joint_and_ltail(a_n, kind, gdat, k4):
    """The 2716 joint semantics: gate point strictly above Ltail."""
    if 0 < a_n < 1:
        lt = k4 * mp.sqrt(a_n) / (1 - mp.sqrt(a_n))
        return bool(r16.gate_has_point_above(kind, gdat, lt)), float(lt)
    return False, None


def main() -> None:
    d32 = json.loads(SRC32.read_text())
    d33 = json.loads(SRC33.read_text())
    d16 = json.loads(SRC16.read_text())

    idx32 = {(r["gamma"], r["N"], r["n"]): r for r in d32["rows"]}
    a16 = {(r["gamma"], r["N"], r["n"]): r for r in d16["rows"]}

    # ---------------- anchor a1: 2033 rows bitwise == 2032 primary -------
    a1_bad = 0
    for o in d33["owners"]:
        for row in o["rows"]:
            g = idx32[(o["gamma"], o["N"], row["n"])]["dxi0.02"]
            for k in ("C", "b", "det", "lambda"):
                if g[k] != row[k]:
                    a1_bad += 1
    assert a1_bad == 0, a1_bad

    # ---------------- anchor a2: lambda == b/C bitwise -------------------
    a2_bad = 0
    for r in d32["rows"]:
        for tag in ("dxi0.02", "dxi0.01"):
            g = r[tag]
            if g["lambda"] != g["b"] / g["C"]:
                a2_bad += 1
    assert a2_bad == 0, a2_bad

    # ---------------- anchor a3: 2716 A_n fields reproduced exactly ------
    a3_bad = 0
    for o in d33["owners"]:
        gamma, N = o["gamma"], o["N"]
        H = f2m(o["H"])
        dec = o["decay"]
        c4, cc2 = f2m(dec["base_C4"]), f2m(dec["correction_C2"])
        beta = 4 * Cspec * (mpf(3) / 4) ** N / M_FLOOR
        for row in o["rows"]:
            n = row["n"]
            ref = a16[(gamma, N, n)]
            for k4, key in ((H ** 4, "A_n_old_geom"),
                            (D_2710, "A_n_new_geom")):
                a_n = (beta * k4 * TWO_PI_12
                       * (r16.Q ** n * c4 * cc2) ** 2 / M_FLOOR)
                if float(a_n) != ref[key]:
                    a3_bad += 1
    assert a3_bad == 0, a3_bad

    # ---------------- channel flip-budget ledger (all rows x 2 grids) ----
    ledger = []
    for r in d32["rows"]:
        row_entry = {"gamma": r["gamma"], "N": r["N"], "n": r["n"],
                     "owner_cardinality": r["owner_cardinality"],
                     "known_zero_count": r["known_zero_count"],
                     "radius": r["radius"], "sign_stable": r["sign_stable"]}
        for tag in ("dxi0.02", "dxi0.01"):
            row_entry[tag] = budgets(r[tag])
        ledger.append(row_entry)

    # ---------------- two-grid honest joint ------------------------------
    joint_fine = []
    n3_both_grids = []
    for o in d33["owners"]:
        gamma, N = o["gamma"], o["N"]
        H = f2m(o["H"])
        dec = o["decay"]
        c4, cc2 = f2m(dec["base_C4"]), f2m(dec["correction_C2"])
        beta = 4 * Cspec * (mpf(3) / 4) ** N / M_FLOOR
        h4 = H ** 4
        p4_ok = 2 * mp.mpf(gamma) <= mpf(2) ** (N + 1)
        for n in range(5):
            row32 = idx32[(gamma, N, n)]
            out = {"gamma": gamma, "N": N, "n": n, "p4_shell_ok": bool(p4_ok)}
            for k4, geom in ((h4, "old"), (D_2710, "new")):
                a_n = (beta * k4 * TWO_PI_12
                       * (r16.Q ** n * c4 * cc2) ** 2 / M_FLOOR)
                a_s = SENS_32 * a_n
                for tag in ("dxi0.02", "dxi0.01"):
                    g = row32[tag]
                    kind, gdat = r16.gate_branches(f2m(g["C"]), f2m(g["b"]),
                                                   f2m(g["det"]))
                    j, lt = joint_and_ltail(a_n, kind, gdat, k4)
                    js, _ = joint_and_ltail(a_s, kind, gdat, k4)
                    cell = out.setdefault(geom, {})
                    cell[tag] = {
                        "branch": kind,
                        "Lplus": (float(gdat["Lplus"])
                                  if "Lplus" in gdat else None),
                        "Ltail": lt,
                        "joint": j, "joint_sens": js,
                    }
            joint_fine.append(out)
            if n == 3 and (gamma, N) in CANDIDATES:
                led = next(e for e in ledger if e["gamma"] == gamma
                           and e["N"] == N and e["n"] == n)
                n3_both_grids.append({
                    "gamma": gamma, "N": N, "p4": bool(p4_ok),
                    "joint_new_pri": out["new"]["dxi0.02"]["joint"],
                    "joint_new_fin": out["new"]["dxi0.01"]["joint"],
                    "joint_new_fin_sens": out["new"]["dxi0.01"]["joint_sens"],
                    "joint_old_fin": out["old"]["dxi0.01"]["joint"],
                    "branch_fin": out["new"]["dxi0.01"]["branch"],
                    "Lplus_fin": out["new"]["dxi0.01"]["Lplus"],
                    "eps_unified_pri": led["dxi0.02"]["eps_unified"],
                    "eps_unified_fin": led["dxi0.01"]["eps_unified"]})

    # ---------------- candidate focus blocks ------------------------------
    candidates = []
    for gamma, N in CANDIDATES:
        r32 = idx32[(gamma, N, 3)]
        blk = {"gamma": gamma, "N": N, "n": 3,
               "owner_cardinality": r32["owner_cardinality"],
               "known_zero_count": r32["known_zero_count"],
               "radius": r32["radius"],
               "prime_book_at_n3": d32["prime_book"]["3"]}
        for tag in ("dxi0.02", "dxi0.01"):
            g = r32[tag]
            (a0, a1, a2), (p0, p1, p2) = channels(g)
            kind, gdat = r16.gate_branches(f2m(g["C"]), f2m(g["b"]),
                                           f2m(g["det"]))
            blk[tag] = {
                "C": g["C"], "b": g["b"], "D": g["D"], "det": g["det"],
                "lambda": g["lambda"], "branch": kind,
                "Lplus": (float(gdat["Lplus"]) if "Lplus" in gdat else None),
                "arch": [a0, a1, a2], "prime": [p0, p1, p2],
                **budgets(g),
            }
        candidates.append(blk)

    out = {
        "record": 2717,
        "title": "G1 swing 2a: P5 n=3 probe -- channel flip budgets and "
                 "two-grid honest joint (paper arithmetic on stored rows)",
        "scope": "sampled-grade margin ledger over stored record-2032 rows; "
                 "NOT certified enclosures; no owner change; no producer GO",
        "inputs": {
            "source_2032": "results/2032_gate_row_search.json",
            "source_2032_sha256":
                hashlib.sha256(SRC32.read_bytes()).hexdigest(),
            "source_2033": "results/2033_gate_tail_pairing.json",
            "source_2716": "results/2716_g1_joint_acceptance_repricing.json",
        },
        "anchors": {
            "a1_bitwise_2033_vs_2032_mismatches": a1_bad,
            "a2_lambda_eq_b_over_C_mismatches": a2_bad,
            "a3_2716_field_mismatches": a3_bad,
        },
        "candidate_rows": CANDIDATES,
        "candidates": candidates,
        "n3_joint_at_both_grids": n3_both_grids,
        "ledger_rows": len(ledger),
        "ledger": ledger,
        "joint_fine": joint_fine,
        "producer_go": False, "family_reopened": False, "rh_claim": False,
    }
    (ROOT / "results/2717_p5_n3_probe.json").write_text(
        json.dumps(out, indent=2) + "\n")

    print(json.dumps({
        "anchors": out["anchors"],
        "candidates": [
            {"gamma": c["gamma"], "N": c["N"],
             "branch_pri": c["dxi0.02"]["branch"],
             "branch_fin": c["dxi0.01"]["branch"],
             "eps_C_pri": c["dxi0.02"]["eps_C"],
             "eps_Delta_pri": c["dxi0.02"]["eps_Delta"],
             "eps_unified_pri": c["dxi0.02"]["eps_unified"],
             "eps_unified_fin": c["dxi0.01"]["eps_unified"]}
            for c in candidates],
        "n3_joint_both_grids": n3_both_grids,
    }, indent=2))
    print("RESULT 2717 anchors OK (a1 bitwise, a2 bitwise, a3 exact); "
          "ledger rows=%d; candidates=%d; artifact written"
          % (len(ledger), len(candidates)))


if __name__ == "__main__":
    main()
