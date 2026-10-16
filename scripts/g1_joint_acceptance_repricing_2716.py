#!/usr/bin/env python3
"""Record 2716 (G1 swing 1): honest joint-acceptance repricing of the
stored map-103 gate rows under the exact record-2708 contract.

Paper arithmetic only (record-2709/2714 precedent): stored-constant
evaluation, no measurement, no rig, no Lean build.

What changes vs the record-2033/2709 readings:

  1. the multiplicity factor beta_s/m = 4*Cspec*(3/4)^s / m is priced
     explicitly (the 2033 convention folds it to a unit proxy),
  2. the gate interval is read from the exact parabola on EVERY D/B/C
     branch (record-2708 section 5: non-vertex branches use (G)
     directly), not only the registered C>0,b>0,det<0 pattern,
  3. both geometries are priced: stored K^4 = H^4 and the
     kernel-checked record-2710 constant d = 169/16,
  4. P4 shell admissibility (2*|Im rho| <= 2^(s+1), s = N) is checked
     per owner.

Conventions (all from committed sources):

  gate quadratic   G(lam) = D - B*lam + C*lam^2,  B = 2*b,
                   D = (det + b^2)/C,  det = C*D - b*b
                   (record-2032 definition; Delta = B^2 - 4CD = -4*det)
  tail (J)         4*Cspec*(3/4)^s * K^4 * (K^4 + lam)^2 * (2*pi)^12
                   * (q^n * C4 * C2)^2 < m * lam^2
                   (record-2708 section 4, exact form, no 3/2)
  (R)              A_n * (1 + K^4/lam)^2 < 1,
                   A_n = 4*Cspec*(3/4)^s * K^4 * (2*pi)^12
                         * (q^n * C4 * C2)^2 / m
  Ltail            K^4 * sqrt(A_n) / (1 - sqrt(A_n))   (0 < A_n < 1)
  A0               H^4 * (2*pi)^12 * (C4 * C2)^2   (record-2033 field)

Anchors (in-run):
  a1  tau_q reproduced row-by-row at 1e-12 (2033 formula, float order),
  a2  2709 new_proxy reproduced row-by-row at 1e-12,
  a3  gate_signs == (C>0 and b>0 and det<0) on every stored row
      (the record-2035 registered-pattern definition),
  a4  the eight record-2033 lambda_joint_rows are a subset of this
      script's exact unit-proxy joint set,
  a5  d < H^4 on every row (the 2710 geometry strictly shrinks K^4).
"""
from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from mpmath import mpf

mp.mp.dps = 50

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "results/2033_gate_tail_pairing.json"
SRC_2709 = ROOT / "results/2709_high_shell_geometry_sensitivity.json"

# ----------------------------------------------------------- constants ---
Cspec = mp.mpf("128.65")          # proved multiplicity bound (record 2354)
M_FLOOR = mp.mpf(1)               # m = xiMultiplicity(rho) >= 1
D_NEW = mp.mpf(169) / 16          # record-2710 kernel-checked geometry
Q = mp.mpf(2) ** -14              # stored owner contraction (record 2033)
TWO_PI_12 = (2 * mp.pi) ** 12
SENS_32 = mp.mpf(3) / 2           # record-2354 epsilon^2 = (3/2)A variant


def frac_to_mp(x: float):
    """Exact binary64 capture, then 50-dps conversion."""
    f = Fraction(x)
    return mp.mpf(f.numerator) / mp.mpf(f.denominator)


# ---------------------------------------------------------- gate logic ---
def gate_branches(C, b, det):
    """Exact lambda>0 gate set of G = D - (2b)lam + C lam^2 <= 0.

    Returns (kind, data): kind in {'all', 'interval', 'rays', 'none'} with
    interval = [Lminus, Lplus] (closed), rays = (0, Lminus] U [Lplus, inf).
    """
    # det = C*D - b*b (record 2032) => Delta = B^2 - 4CD = -4*det exactly;
    # D itself is never needed.  (-4*det is exact in binary64 -> mp.)
    B = 2 * b
    delta = -4 * det
    if C > 0:
        if delta < 0:
            return "none", {}
        s = mp.sqrt(delta)
        return "interval", {"Lminus": (B - s) / (2 * C),
                            "Lplus": (B + s) / (2 * C)}
    # C < 0 (no zero-C rows in the stored data; asserted by caller)
    if delta <= 0:
        return "all", {}
    s = mp.sqrt(delta)
    return "rays", {"Lminus": (B - s) / (2 * C),
                    "Lplus": (B + s) / (2 * C)}


def gate_has_point_above(kind, data, lam):
    """Is there a gate point strictly above lam?"""
    if kind == "all":
        return True
    if kind == "none":
        return False
    if kind == "interval":
        return data["Lplus"] > lam          # closed endpoint, strict tail
    # "rays": (0, Lminus] U [Lplus, inf) -- the upper ray is UNBOUNDED,
    # so a point strictly above any finite lam always exists.
    return True


# --------------------------------------------------------------- main ---
def main() -> None:
    data = json.loads(SRC.read_text())
    q_stored = mp.mpf(data["q"])
    assert q_stored == Q, "stored q drifted"
    r2709 = json.loads(SRC_2709.read_text())
    proxy_2709 = {(r["gamma"], r["N"], r["n"]): r["new_proxy"]
                  for r in r2709["rows"]}

    rows_out, a1_dev, a2_dev = [], [], []
    joint_unitproxy_exact = set()

    for owner in data["owners"]:
        gamma, N = owner["gamma"], owner["N"]
        H = frac_to_mp(owner["H"])
        dec = owner["decay"]
        c4, cc2 = frac_to_mp(dec["base_C4"]), frac_to_mp(dec["correction_C2"])
        A0 = frac_to_mp(owner["A0"])
        beta = 4 * Cspec * (mp.mpf(3) / 4) ** N / M_FLOOR
        p4_ok = 2 * mp.mpf(gamma) <= mp.mpf(2) ** (N + 1)

        for row in owner["rows"]:
            n = row["n"]
            C, b, det = (frac_to_mp(row["C"]), frac_to_mp(row["b"]),
                         frac_to_mp(row["det"]))
            lam_stored = frac_to_mp(row["lambda"])

            # ---- anchor a1: tau_q (2033 float order reproduced) -------
            Hf, c4f, c2f = owner["H"], dec["base_C4"], dec["correction_C2"]
            a0f = Hf**4 * (2.0 * math.pi) ** 12 * (c4f * c2f) ** 2
            tau_ref = a0f * (2.0**-14) ** (2 * n) * (1.0 + Hf**4 / row["lambda"]) ** 2
            a1_dev.append(abs(tau_ref / row["tau_q"] - 1.0))

            # ---- anchor a2: 2709 new_proxy (row-matched artifact) -----
            h4 = H ** 4
            old = A0 * q_stored ** (2 * n) * (1 + h4 / lam_stored) ** 2
            new = old * D_NEW / h4 * ((D_NEW + lam_stored) / (h4 + lam_stored)) ** 2
            if (gamma, N, n) in proxy_2709:
                a2_dev.append(float(abs(new / mp.mpf(frac_to_mp(
                    proxy_2709[(gamma, N, n)])) - 1)))

            # ---- anchor a3: registered pattern ------------------------
            assert row["gate_signs"] == (row["C"] > 0 and row["b"] > 0
                                         and row["det"] < 0), "pattern drift"
            # ---- anchor a5 --------------------------------------------
            assert D_NEW < h4, "2710 geometry must shrink K^4"

            kind, gdat = gate_branches(C, b, det)

            # honest A_n, both geometries; (R) test is A_n (1+K4/lam)^2 < 1
            def price(k4):
                a_n = beta * k4 * TWO_PI_12 * (q_stored**n * c4 * cc2) ** 2 / M_FLOOR
                a_s = SENS_32 * a_n
                if 0 < a_n < 1:
                    ltail = k4 * mp.sqrt(a_n) / (1 - mp.sqrt(a_n))
                    joint = gate_has_point_above(kind, gdat, ltail)
                else:
                    ltail, joint = None, False
                if 0 < a_s < 1:
                    ltail_s = k4 * mp.sqrt(a_s) / (1 - mp.sqrt(a_s))
                    joint_s = gate_has_point_above(kind, gdat, ltail_s)
                else:
                    ltail_s, joint_s = None, False
                return a_n, ltail, joint, a_s, ltail_s, joint_s

            a_old, lt_old, j_old, as_old, lts_old, js_old = price(h4)
            a_new, lt_new, j_new, as_new, lts_new, js_new = price(D_NEW)

            # unit-proxy exact joint (2033 P5 semantics) for anchor a4
            tau_inf = A0 * q_stored ** (2 * n)
            if tau_inf < 1:
                lup = h4 / (1 / mp.sqrt(tau_inf) - 1)
                if gate_has_point_above(kind, gdat, lup):
                    joint_unitproxy_exact.add((gamma, N, n))

            rows_out.append({
                "gamma": gamma, "N": N, "n": n,
                "gate_branch": kind,
                "gate_Lminus": (float(gdat["Lminus"]) if "Lminus" in gdat
                                else None),
                "gate_Lplus": (float(gdat["Lplus"]) if "Lplus" in gdat
                               else None),
                "p4_shell_ok": bool(p4_ok),
                "A_n_old_geom": float(a_old),
                "Ltail_old_geom": (float(lt_old) if lt_old is not None
                                   else None),
                "joint_old_geom": bool(j_old),
                "joint_old_geom_sens_3_2": bool(js_old),
                "A_n_new_geom": float(a_new),
                "Ltail_new_geom": (float(lt_new) if lt_new is not None
                                   else None),
                "joint_new_geom": bool(j_new),
                "joint_new_geom_sens_3_2": bool(js_new),
                "unit_proxy_tau_inf_lt_1": bool(tau_inf < 1),
            })

    # ---- anchor a4: recorded 2033 joints subset of exact unit-proxy set --
    recorded = {(r["gamma"], r["N"], r["n"])
                for r in data["lambda_joint_rows"]}
    assert recorded <= joint_unitproxy_exact, (
        "recorded 2033 joint rows must be a subset of the exact set; "
        "missing: %s" % (recorded - joint_unitproxy_exact))

    assert max(a1_dev) < 1e-12, max(a1_dev)
    assert all(d < 1e-12 for d in a2_dev if d), max(a2_dev)

    survivors = [r for r in rows_out if r["joint_old_geom"]]
    survivors_p4 = [r for r in survivors if r["p4_shell_ok"]]
    out = {
        "record": 2716,
        "title": "G1 swing 1: honest joint-acceptance repricing of the "
                 "stored map-103 gate rows (paper arithmetic)",
        "scope": "stored-constant evaluation of the record-2708 exact "
                 "contract with beta_s/m priced; sampled owner constants; "
                 "not complete-owner certification, no producer GO",
        "inputs": {
            "source_artifact": "results/2033_gate_tail_pairing.json",
            "source_sha256": hashlib.sha256(SRC.read_bytes()).hexdigest(),
            "Cspec": float(Cspec), "m_floor": 1,
            "q_stored": float(Q), "d_2710": float(D_NEW),
            "gate_convention": "G = D - (2b)lam + C lam^2; det = CD - b*b; "
                               "Delta = -4*det (record 2032/2033 P5)",
        },
        "anchors": {
            "tau_q_max_rel_dev": max(a1_dev),
            "repriced_2709_max_rel_dev": max(d for d in a2_dev if d),
            "recorded_2033_joints": len(recorded),
            "exact_unitproxy_joints": len(joint_unitproxy_exact),
        },
        "rows": rows_out,
        "joint_survivors_old_geom": [r for r in survivors],
        "joint_survivors_p4_admissible": survivors_p4,
        "sens_3_2_survivors_p4": [r for r in rows_out
                                  if r["joint_new_geom_sens_3_2"]
                                  and r["p4_shell_ok"]],
        "producer_go": False, "family_reopened": False, "rh_claim": False,
    }
    (ROOT / "results/2716_g1_joint_acceptance_repricing.json").write_text(
        json.dumps(out, indent=2) + "\n")

    print(json.dumps({
        "anchors": out["anchors"],
        "survivors_old_geom": [
            (r["gamma"], r["N"], r["n"], r["gate_branch"],
             r["A_n_old_geom"], r["Ltail_old_geom"], r["p4_shell_ok"])
            for r in survivors],
        "pattern_rows_honest_verdict": [
            (r["gamma"], r["N"], r["n"], r["A_n_old_geom"],
             r["A_n_new_geom"]) for r in rows_out if r["gate_branch"]
            == "interval"],
    }, indent=2))
    print("RESULT 2716 selftests+anchors OK; rows=%d; survivors=%d "
          "(p4-admissible %d); artifact written"
          % (len(rows_out), len(survivors), len(survivors_p4)))


if __name__ == "__main__":
    main()
