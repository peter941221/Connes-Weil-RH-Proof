#!/usr/bin/env python3
"""2719 - G2 complete-owner identification at the two n=3 candidate balls.

Rung (ii) of the named map-103 reopen probe (records 2716/2717/2718):
identifies the stored record-1980 known-zero lists with the COMPLETE
source-zero set in the closed formal balls, so that the record-2718
model-grade gate sign certificate speaks at the complete owner without
re-measurement (if nothing is missing) -- or proves an owner gap and
forces the re-measurement swing (if something is).

Method: the record-2245 count-brick discipline, applied at the candidate
balls.  Every check is in-run:

  E0  stored-metadata anchor: formal_radius and the rebuilt known list
      match the stored record-2032 row fields (19 / 48 known,
      27 / 56 owner cardinality) bitwise on the floats, and the
      independent zetazero walk reproduces the op list elementwise.
  E1  pin-zero-ness: |zeta(1/2 +- i gamma_k)| < 1e-10 at dps 60 for
      every listed ordinate, upper AND conjugate, evaluated directly.
  E2  exact upper count: the unwrapped-phase identity
      N(T) = (theta(T) + Phi(T))/pi at T = t_plus, residual <= 1e-12
      against the listed upper-half count.
  E3  exact conjugate-window count at T = t_conj against the listed
      conjugate count, residual <= 1e-12.
  E4  independent Hardy-Z sign-change enumeration agrees with the listed
      upper ordinates (count + paired set equality at 1e-9).
  E5  Trudgian unconditional upper bounds (2014 primary, 2012 secondary)
      at both edges are >= the exact counts; validity T >= e checked.
  E6  Platt-Trudgian import applicability: every point of the ball has
      |Im| <= Im(rho) + R < 3e12, so ALL in-ball source zeros lie on the
      critical line and are simple (single vanishing factors suffice).
  E7  ball-edge margins: nearest excluded zero strictly outside the
      sphere by > 1e-6, nearest included strictly inside by > 1e-6 --
      the loop's 1e-10 membership pad is inert.
  E8  environment audit: zetazero(4) = 30.424876125859513210 and the
      spurious 1994 pin 27.67032193035704 carries |zeta| = 2.845 (>= the
      pin bar: correctly rejected by E1 semantics).
  E9  owner separation: the assembled owner's minimum pairwise
      separation (0.05 = |rho - gamma_1|) exceeds the 1e-10 dedup and
      membership tolerances by >= 1e5.

Verdict per row: all green => the stored known set IS the complete
in-ball source-zero set => the record-2718 certificates are
complete-owner certificates (zero-set side) with no channel change.

Cited imports (registered numerically first in record 2245; re-registered
here with the same constants):
  - Trudgian II (2014): |S(T)| <= 0.111 log T + 0.275 log log T + 2.450,
    T >= e (J. Number Theory 134, Theorem 1, arXiv:1208.5846).
  - Trudgian I (2012) historical variant |S(T)| <= 0.17 log T + 1.998.
  - Platt-Trudgian (2021): all zeros with 0 < Im <= 3e12 are simple and
    on the critical line; exact counts certified (Bull. LMS 53).
  - Riemann-von Mangoldt: N(T) = 1 + theta(T)/pi + S(T).

Owner convention (committed lane, record-2245 impact note): the source
zeros are the nontrivial zeros (completed-source convention); the
functional-equation orbit of rho and the healthy-target/real-axis pins
are separate construction nodes, not enumerated zeros.

Writes results/2719_g2_complete_owner_id.json.  No producer GO, no
map-103 reopening, no RH claim; the Lean-side finite-set -> shell-prefix
identification remains the separate formal brick.
"""

import hashlib
import json
import math
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op  # noqa: E402
import routea_weighted_zero_owner_count_brick_2245 as m45  # noqa: E402

RECORD = 2719
DATE = "2026-10-16"
DPS = 60
PIN_BAR = 1e-10
RESIDUAL_BAR = 1e-12
SET_EQ_TOL = 1e-9
EDGE_MARGIN_BAR = 1e-6
PAD = 1e-10
SEP_BAR = 1e5  # min_separation must exceed PAD by at least this factor
PT_HEIGHT_LIMIT = 3.0e12

CANDIDATES = [
    {"gamma": 14.134725141734693, "re": 0.55, "N": 4,
     "stored_known": 19, "stored_owner_cardinality": 27,
     "stored_radius": 48.208904068660146},
    {"gamma": 21.022039638771556, "re": 0.55, "N": 5,
     "stored_known": 48, "stored_owner_cardinality": 56,
     "stored_radius": 87.0719873427753},
]

OUTPUT = ROOT / "results" / "2719_g2_complete_owner_id.json"

TRUE_GAMMA_4 = "30.424876125859513210"
SPURIOUS_PIN = "27.67032193035704"


def independent_walk(rho, radius):
    """Own zetazero walk with the record-1980 membership semantics."""
    found = []
    k = 1
    while k <= 300:
        zero = mp.zetazero(k)
        zf = complex(float(mp.re(zero)), float(mp.im(zero)))
        if zf.imag - rho.imag > radius + 1.0:
            break
        if abs(zf - rho) <= radius + PAD:
            found.append(zf)
        zc = zf.conjugate()
        if abs(zc - rho) <= radius + PAD:
            found.append(zc)
        k += 1
    return found, k - 1


def pin_ordinates(ordinates):
    rows = []
    for g in ordinates:
        gf = mp.mpf(g)
        for sign, tag in ((1, "upper"), (-1, "conj")):
            val = abs(mp.zeta(mp.mpc(mp.mpf("0.5"), sign * gf)))
            rows.append({"gamma": g, "sign": tag,
                         "abs_zeta": float(val),
                         "ok": bool(val < PIN_BAR)})
    return rows


def exact_count(t_float):
    t = mp.mpf(t_float)
    theta = mp.siegeltheta(t)
    s_phase = m45.s_numeric(t)
    identity = theta / mp.pi + s_phase
    return {"t": t_float,
            "theta_over_pi": float(theta / mp.pi),
            "S_phase": float(s_phase),
            "identity_value": float(identity),
            "count": int(mp.floor(identity)),
            "residual_from_integer": float(identity - mp.floor(identity))}


def trudgian_uppers(t_float):
    t = mp.mpf(t_float)
    theta = mp.siegeltheta(t)
    n14 = 1 + theta / mp.pi + m45.trudgian_2014(t)
    n12 = 1 + theta / mp.pi + m45.trudgian_2012(t)
    return {"t": t_float,
            "upper_2014": float(n14), "floor_2014": int(mp.floor(n14)),
            "upper_2012": float(n12), "floor_2012": int(mp.floor(n12)),
            "validity_T_ge_e": bool(t >= mp.e)}


def hardy_z_scan(t_float):
    heights = m45.zeros_by_siegelz(mp.mpf(t_float))
    return [float(h) for h in heights]


def edge_margins(rho, radius, known, n_walk):
    """In/out sphere margins around the membership boundary."""
    in_margin = min(radius - abs(z - rho) for z in known)
    out = []
    k = 1
    while k <= n_walk + 6:
        zero = mp.zetazero(k)
        zf = complex(float(mp.re(zero)), float(mp.im(zero)))
        if zf.imag - rho.imag <= radius + 1.0:
            if abs(zf - rho) > radius + PAD:
                out.append(abs(zf - rho) - radius)
            zc = zf.conjugate()
            if abs(zc - rho) > radius + PAD:
                out.append(abs(zc - rho) - radius)
            k += 1
        else:
            out.append(abs(zf - rho) - radius)
            out.append(abs(zf.conjugate() - rho) - radius)
            k += 1
            if len(out) >= 4:
                break
    return {"min_included_margin": float(in_margin),
            "min_excluded_margin": float(min(out)),
            "bar": EDGE_MARGIN_BAR,
            "ok": bool(in_margin > EDGE_MARGIN_BAR
                       and min(out) > EDGE_MARGIN_BAR)}


def identify_row(cand):
    rho = complex(cand["re"], cand["gamma"])
    radius = op.formal_radius(rho, cand["N"])
    row = {"gamma": cand["gamma"], "N": cand["N"], "rho": [rho.real, rho.imag]}

    # E0: stored-metadata anchor.
    row["radius"] = radius
    row["radius_matches_stored"] = bool(
        radius == cand["stored_radius"])
    known_ref = op.known_source_zeros_in_ball(rho, radius)
    known_mine, n_walk = independent_walk(rho, radius)
    row["walk_indices_processed"] = n_walk
    row["known_matches_stored_count"] = bool(
        len(known_ref) == cand["stored_known"])
    row["mirror_elementwise_equal"] = bool(
        len(known_ref) == len(known_mine)
        and all(a == b for a, b in zip(known_ref, known_mine)))

    uppers = [z for z in known_ref if z.imag > 0]
    conjs = [z for z in known_ref if z.imag < 0]
    up_gamma = sorted(z.imag for z in uppers)
    row["n_upper_listed"] = len(uppers)
    row["n_conj_listed"] = len(conjs)

    # Exact geometry (delta-corrected critical-line window).
    delta = abs(rho.real - 0.5)
    W = math.sqrt(radius * radius - delta * delta)
    t_plus = rho.imag + W
    t_conj = W - rho.imag
    row["geometry"] = {"delta": delta, "W": W, "t_plus": t_plus,
                       "t_conj": t_conj,
                       "t_minus_signed": rho.imag - W}

    # E2/E3: exact phase-identity counts.
    cnt_plus = exact_count(t_plus)
    cnt_conj = exact_count(t_conj)
    row["count_t_plus"] = cnt_plus
    row["count_t_conj"] = cnt_conj
    row["E2_exact_upper_count"] = bool(
        cnt_plus["count"] == len(uppers)
        and abs(cnt_plus["residual_from_integer"]) <= RESIDUAL_BAR)
    row["E3_exact_conj_count"] = bool(
        cnt_conj["count"] == len(conjs)
        and abs(cnt_conj["residual_from_integer"]) <= RESIDUAL_BAR)

    # E4: independent Hardy-Z enumeration.
    hz = hardy_z_scan(t_plus)
    in_win = [h for h in hz if h <= t_plus + SET_EQ_TOL]
    paired = (len(in_win) == len(up_gamma)
              and all(abs(a - b) < SET_EQ_TOL
                      for a, b in zip(sorted(in_win), up_gamma)))
    row["hardy_z_count"] = len(in_win)
    row["hardy_z_first_beyond"] = (
        min((h for h in hz if h > t_plus + SET_EQ_TOL), default=None))
    row["E4_hardy_z_agreement"] = bool(paired)

    # E5: Trudgian unconditional uppers.
    tg_plus = trudgian_uppers(t_plus)
    tg_conj = trudgian_uppers(t_conj)
    row["trudgian_t_plus"] = tg_plus
    row["trudgian_t_conj"] = tg_conj
    row["E5_trudgian_upper_ge_exact"] = bool(
        tg_plus["floor_2014"] >= cnt_plus["count"]
        and tg_conj["floor_2014"] >= cnt_conj["count"]
        and tg_plus["validity_T_ge_e"] and tg_conj["validity_T_ge_e"])

    # E6: Platt-Trudgian applicability (whole ball below the certified
    # height limit).
    row["E6_PT_applicability"] = bool(
        rho.imag + radius < PT_HEIGHT_LIMIT)
    row["pt_height_limit"] = PT_HEIGHT_LIMIT

    # E7: ball-edge margins.
    row["edge_margins"] = edge_margins(rho, radius, known_ref, n_walk)
    row["E7_edge_margins"] = row["edge_margins"]["ok"]

    # E8: environment audit.
    z4 = abs(mp.im(mp.zetazero(4)) - mp.mpf(TRUE_GAMMA_4))
    sp = abs(mp.zeta(mp.mpc(mp.mpf("0.5"), mp.mpf(SPURIOUS_PIN))))
    row["E8_zetazero4_ok"] = bool(z4 < 1e-10)
    row["E8_spurious_rejected"] = bool(sp > PIN_BAR)
    row["E8_values"] = {"zetazero4_gap": float(z4),
                        "spurious_abs_zeta": float(sp)}

    # E9: owner separation.
    owner, targets, radius2, _ = op.build_owner(rho, cand["N"])
    row["build_owner_radius_matches"] = bool(radius2 == radius)
    row["owner_cardinality"] = len(owner)
    row["owner_cardinality_matches_stored"] = bool(
        len(owner) == cand["stored_owner_cardinality"])
    min_sep = op.min_separation(owner)
    row["min_separation"] = float(min_sep)
    row["E9_separation_ok"] = bool(min_sep > PAD * SEP_BAR)
    row["n_targets"] = len(targets)

    # E1: pin-zero-ness on every listed ordinate (both signs).
    pins = pin_ordinates(up_gamma)
    row["pins"] = pins
    row["pins_all_ok"] = all(p["ok"] for p in pins)
    row["pins_worst"] = max(p["abs_zeta"] for p in pins)
    row["n_pin_evaluations"] = len(pins)

    checks = ["radius_matches_stored", "known_matches_stored_count",
              "mirror_elementwise_equal", "E2_exact_upper_count",
              "E3_exact_conj_count", "E4_hardy_z_agreement",
              "E5_trudgian_upper_ge_exact", "E6_PT_applicability",
              "E7_edge_margins", "E8_zetazero4_ok", "E8_spurious_rejected",
              "E9_separation_ok", "build_owner_radius_matches",
              "owner_cardinality_matches_stored", "pins_all_ok"]
    row["failed_checks"] = [c for c in checks if not row[c]]
    row["verdict"] = ("COMPLETE-OWNER-IDENTIFIED"
                      if not row["failed_checks"] else "OWNER-GAP-FOUND")
    return row


def sha256_of(path):
    h = hashlib.sha256()
    h.update(Path(path).read_bytes())
    return h.hexdigest()


def main():
    mp.mp.dps = DPS
    rows = [identify_row(cand) for cand in CANDIDATES]
    all_complete = all(r["verdict"] == "COMPLETE-OWNER-IDENTIFIED"
                       for r in rows)
    result = {
        "record": RECORD,
        "date": DATE,
        "status": ("G2-COMPLETE-OWNER-IDENTIFIED"
                   if all_complete else "G2-OWNER-GAP-FOUND"),
        "dps": DPS,
        "rows": rows,
        "imports": {
            "trudgian_2014": {
                "source": "T. S. Trudgian, J. Number Theory 134 (2014), "
                          "Theorem 1 (arXiv:1208.5846)",
                "bound": "|S(T)| <= 0.111 log T + 0.275 log log T + 2.450",
                "validity": "T >= e",
                "first_registered": "record 2245",
            },
            "trudgian_2012": {
                "source": "comparison table of arXiv:1208.5846",
                "bound": "|S(T)| <= 0.17 log T + 1.998",
                "validity": "T >= e",
                "first_registered": "record 2245",
            },
            "platt_trudgian_2021": {
                "source": "D. Platt, T. Trudgian, Bull. LMS 53 (2021) "
                          "792-797",
                "content": "all zeros with 0 < Im <= 3e12 are simple and "
                           "on the critical line; exact counts certified",
                "role": "all in-ball source zeros lie on the critical "
                        "line and are simple",
                "first_registered": "record 2245",
            },
            "riemann_von_mangoldt": {
                "identity": "N(T) = 1 + theta(T)/pi + S(T); with Z real, "
                            "N(T) = (theta(T) + Phi(T))/pi exactly",
                "first_registered": "record 2245",
            },
        },
        "owner_convention": ("source zeros = nontrivial zeros "
                             "(completed-source convention); orbit and "
                             "healthy-target/real-axis pins are separate "
                             "construction nodes (record-2245 impact "
                             "note)"),
        "nonclaims": [
            "cited-import + numeric certificate at model grade; no Lean "
            "theorem (the finite-set -> shell-prefix identification in "
            "Lean is the separate formal brick)",
            "the owner-model constants (rho floats, radius convention) "
            "are the stored record-1980 model constants",
            "no producer GO, no gate sign change, no SourceRH, no RH "
            "claim",
            "P3 (certified C4/C2) and P4 (shell identification in Lean) "
            "unchanged",
        ],
        "provenance": {
            "script": "scripts/g2_complete_owner_id_2719.py",
            "script_sha256": sha256_of(ROOT / "scripts"
                                       / "g2_complete_owner_id_2719.py"),
            "producer_modules": {
                "fourpoint_actual_owner_1980.py": sha256_of(
                    ROOT / "scripts" / "fourpoint_actual_owner_1980.py"),
                "routea_weighted_zero_owner_count_brick_2245.py":
                    sha256_of(ROOT / "scripts"
                              / "routea_weighted_zero_owner_count_brick_"
                              "2245.py"),
            },
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({
        "status": result["status"],
        "rows": [{"gamma": r["gamma"], "N": r["N"],
                  "verdict": r["verdict"],
                  "n_upper": r["n_upper_listed"],
                  "exact_t_plus": r["count_t_plus"]["count"],
                  "n_conj": r["n_conj_listed"],
                  "exact_t_conj": r["count_t_conj"]["count"],
                  "failed": r["failed_checks"]} for r in rows],
    }, indent=2))


if __name__ == "__main__":
    main()
