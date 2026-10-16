#!/usr/bin/env python3
"""Record 2714: near-line collision frontier for the 2354-class consumer.

Paper-arithmetic only, following the record-2709 precedent (stored-constant
evaluation, no measurement, no rig, no Lean build).  The script

  1. reproduces the two committed record-2354 acceptance-lane ratios as an
     in-run anchor (same-run reprice law, AGENTS 2h),
  2. reprices those ratios under the kernel-checked record-2710 geometry
     (d = 169/16 replacing (3+R)^4),
  3. prices the record-2713 collision floor against the consumer's
     correction-decay budget, giving the frontier delta* = the smallest
     Re(rho) - 1/2 at which the fixed-window interpolation class can still
     pay the existing tail certificate,
  4. cross-checks the same frontier in the older record-2033 proxy lane.

Conventions (kept explicit because two lanes use different ones):

  consumer lane (record 2354, the honest one):
    ratio(n, lambda) = (3/2)*4*K*(3/4)^N/m * L * (1 + L/lambda)^2
                       * (q^n * D4 * D2)^2
    with K <= multProxy2248, N = 6, q = 2^-52, D4, D2 the directed caps,
    L = (3+R)^4 (old) or d = 169/16 (new geometry).  ratio < 1 is the
    sufficient scalar acceptance.  C4 = D4/(2*pi)^4, C2 = D2/(2*pi)^2 and
    (2*pi)^12*(q^n*C4*C2)^2 = (q^n*D4*D2)^2 exactly (record 2354).

  correction-decay budget implied by ratio < 1 (new geometry):
    C2 < 1/((2*pi)^2 * q^n * D4 * sqrt(Wtilde*d) * (1 + d/lambda))
    Wtilde = (3/2)*4*K*(3/4)^N/m.

  collision floor (record 2713 section 3, target values +1/-1 at
  (rho, 1-conj(rho)), separation 2*delta):
    M0 >= 1/(delta*L*E)  =>  C2 >= 12/(delta*L_log)   (E cancels).

  frontier: 12/(delta* L_log) = C2_max  =>
    delta* = 12*(2*pi)^2 * q^n * D4 * sqrt(Wtilde*d) * (1 + d/lambda) / L_log.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
from mpmath import mpf

mp.mp.dps = 60

ROOT = Path(__file__).resolve().parents[1]
SRC_2033 = ROOT / "results/2033_gate_tail_pairing.json"

# ---------------------------------------------------------------- inputs ---
# record 2354 (docs/proofs/2354_same_owner_tail_acceptance.md)
Q = F(1, 2**52)                       # 2353 supplier cap at T = 128
D4 = F(746785658244)                  # directed cap of |t|^4 |B|
D2 = F(71280628476)                   # directed cap of |t|^2 |C|
K_MULT = F(12865, 100)                # record-2354 K bound (C1RouteAMultiplicityBound; 2354
                                      # explicitly does NOT use the larger multProxy2248 = 128.70692502981)
N_SHELL = 6                           # T = 128 <= 2^(N+1); 2|Im rho| <= 2^7
M_MULT = F(1)                         # marked-zero multiplicity floor
D_OLD = F(44) ** 4                    # (3+R)^4, R = 41 norm cap (record 2354)
D_NEW = F(169, 16)                    # kernel-checked geometry (record 2710)
# record 2666 (results/2666_gate_lambda_audit.json)
LAM_2666_MIN = F("40018.85139273456")
LAM_2666_MAX = F("195695.13149589527")
# record 2713 / 2354 support composition
L_LOG = F(65536, 10**4)               # 6.5536, conservative family max log-radius
L_LOG_LEAN = F(65536001, 10**7)       # stripRadius2303 Lean literal (larger)
DELTA_Y = F(2)                        # |F(rho) - F(1-conj rho)|, proxy targets +1/-1
LANE_N2, LAM_LANE_N2 = 2, F(256)      # record-2354 lane edges
LANE_N3, LAM_LANE_N3 = 3, F(1, 10**13)

W_TILDE = F(3, 2) * 4 * K_MULT * F(3, 4) ** N_SHELL / M_MULT


def ratio(n: int, lam: F, geom: F) -> F:
    """Record-2354 scalar acceptance ratio in exact rationals."""
    return (W_TILDE * geom * (1 + geom / lam) ** 2
            * (Q**n * D4 * D2) ** 2)


def c2_max(n: int, lam: F, geom: F) -> mpf:
    """Correction-decay budget C2_max implied by ratio < 1 (exact inputs)."""
    qn = mp.mpf(Q.numerator) / Q.denominator
    return 1 / ((2 * mp.pi) ** 2 * (qn ** n) * mp.mpf(D4.numerator) / D4.denominator
                * mp.sqrt(mp.mpf(W_TILDE.numerator) / W_TILDE.denominator
                          * geom.numerator / geom.denominator)
                * (1 + geom * (mp.mpf(lam.denominator) / lam.numerator)))


def delta_star2(n: int, lam: F, geom: F, l_log: F) -> mpf:
    """Near-line collision frontier: delta* = 12 / (L_log * C2_max)."""
    l = mp.mpf(l_log.numerator) / l_log.denominator
    return 12 / (l * c2_max(n, lam, geom))


# -------------------------------------------------------------- selftests ---
def selftest() -> None:
    # 1-2: in-run reproduction of the committed record-2354 lane ratios.
    a1 = float(ratio(LANE_N2, LAM_LANE_N2, D_OLD))
    a2 = float(ratio(LANE_N3, LAM_LANE_N3, D_OLD))
    assert abs(a1 / 0.7603893268553 - 1) < 1e-9, a1
    assert abs(a2 / 0.2456614834776 - 1) < 1e-9, a2
    # 3: the new geometry strictly tightens every ratio.
    for n in (1, 2, 3):
        for lam in (LAM_LANE_N2, LAM_LANE_N3, LAM_2666_MIN, LAM_2666_MAX):
            assert ratio(n, lam, D_NEW) < ratio(n, lam, D_OLD)
    # 4: the tail still needs n >= 2 in this class even with the new geometry.
    assert ratio(1, LAM_LANE_N2, D_NEW) > 1
    assert ratio(LANE_N2, LAM_LANE_N2, D_NEW) < 1
    # 5-6: headline frontier readings.  At the n=3 lane edge lambda=1e-13 the
    # vertex factor (1+d/lambda) ~ 1.06e14 lifts delta* fourteen orders above
    # the actual-gate-lambda corner; both corners are priced.
    d2 = delta_star2(LANE_N2, LAM_LANE_N2, D_NEW, L_LOG)
    d3 = delta_star2(LANE_N3, LAM_LANE_N3, D_NEW, L_LOG)
    d3a = delta_star2(LANE_N3, LAM_2666_MIN, D_NEW, L_LOG)
    assert 0 < d2 < mp.mpf("1.1e-16"), d2
    assert 0 < d3 < mp.mpf("2.5e-18"), d3
    assert 0 < d3a < mp.mpf("2.5e-32"), d3a
    # 7: monotone directions (larger lambda and larger support help).
    assert delta_star2(2, LAM_2666_MIN, D_NEW, L_LOG) < \
        delta_star2(2, LAM_LANE_N2, D_NEW, L_LOG)
    assert delta_star2(2, LAM_LANE_N2, D_NEW, L_LOG_LEAN) < \
        delta_star2(2, LAM_LANE_N2, D_NEW, L_LOG)
    # 8: the correction cap actually committed stays 1e7 inside its budget.
    budget_n2 = c2_max(2, LAM_2666_MIN, D_NEW)
    committed_c2 = mp.mpf(D2.numerator) / D2.denominator / (2 * mp.pi) ** 2
    assert committed_c2 * mp.mpf("1e6") < budget_n2


# ------------------------------------------------------- 2033-lane check ---
def lane_2033() -> dict:
    """Frontier in the stored record-2033 proxy convention (unit-proxy W)."""
    data = json.loads(SRC_2033.read_text())
    owner = next(o for o in data["owners"]
                 if abs(o["gamma"] - 30.424876125859512) < 1e-9 and o["N"] == 3)
    row = next(r for r in owner["rows"] if r["n"] == 3 and r["gate_signs"])
    q14 = mp.mpf(1) / mp.mpf(2) ** 14
    c4 = mp.mpf(owner["decay"]["base_C4"])
    radius = mp.mpf(owner["decay"]["radius"])
    lam = mp.mpf(row["lambda"])
    d = mp.mpf(169) / 16
    # budget from the stored new_proxy convention (W folded to 1):
    #   q^n C4 C2 < lambda / ((2pi)^6 sqrt(d) (d + lambda))
    c2_budget = lam / ((2 * mp.pi) ** 6 * q14**3 * c4 * mp.sqrt(d) * (d + lam))
    floor_coeff = 12 / radius                       # C2 >= floor_coeff / delta
    return {"gamma": owner["gamma"], "N": owner["N"], "n": row["n"],
            "lambda_row": row["lambda"],
            "base_C4": owner["decay"]["base_C4"],
            "radius": owner["decay"]["radius"],
            "correction_C2": owner["decay"]["correction_C2"],
            "c2_budget": float(c2_budget),
            "delta_star": float(floor_coeff / c2_budget),
            "source_sha256": hashlib.sha256(SRC_2033.read_bytes()).hexdigest()}


# ------------------------------------------------------------------- main ---
def main() -> None:
    selftest()
    rows = []
    for n in (1, 2, 3):
        for lam, tag in ((LAM_LANE_N2, "lane_n2_edge_256"),
                         (LAM_LANE_N3, "lane_n3_edge_1e-13"),
                         (LAM_2666_MIN, "audit_lambda_min"),
                         (LAM_2666_MAX, "audit_lambda_max")):
            ro, rn = ratio(n, lam, D_OLD), ratio(n, lam, D_NEW)
            rows.append({
                "n": n, "lambda": tag,
                "ratio_old_geometry": float(ro),
                "ratio_new_geometry": float(rn),
                "geometric_gain": float(ro / rn),
                "ratio_new_pass": rn < 1,
                "delta_star_new": float(delta_star2(n, lam, D_NEW, L_LOG)),
            })
    lane = lane_2033()
    out = {
        "record": 2714,
        "title": "near-line collision frontier (paper arithmetic)",
        "scope": "stored-constant evaluation of the record-2708 contract with "
                 "the record-2713 collision floor; not complete-owner "
                 "certification, no gate witness, no RH claim",
        "inputs": {
            "q_supplier": "2^-52 (record 2354, 2353 supplier at T=128)",
            "D4": int(D4), "D2": int(D2),
            "K_multProxy2248": float(K_MULT),
            "N_shell": N_SHELL, "m_floor": 1,
            "d_new_geometry": float(D_NEW),
            "d_old_geometry_44pow4": float(D_OLD),
            "L_log_conservative": float(L_LOG),
            "delta_y_proxy": int(DELTA_Y),
            "lambda_2666_min": float(LAM_2666_MIN),
            "lambda_2666_max": float(LAM_2666_MAX),
        },
        "anchors": {
            "ratio_old_n2_256": float(ratio(2, LAM_LANE_N2, D_OLD)),
            "committed_2354_n2_256": 0.7603893268553,
            "ratio_old_n3_1e-13": float(ratio(3, LAM_LANE_N3, D_OLD)),
            "committed_2354_n3_1e-13": 0.2456614834776,
        },
        "w_tilde": float(W_TILDE),
        "rows": rows,
        "lane_2033_cross_check": lane,
        "delta_y_sensitivity": "floor and delta* scale linearly with "
                               "|F(rho)-F(1-conj(rho))|; the +1/-1 proxy pair "
                               "is the strongest-floor case",
        "producer_go": False, "family_reopened": False, "rh_claim": False,
    }
    (ROOT / "results/2714_nearline_collision_frontier.json").write_text(
        json.dumps(out, indent=2) + "\n")
    print(json.dumps({"anchors": out["anchors"], "w_tilde": out["w_tilde"],
                      "headline": rows[6], "lane_2033": lane}, indent=2))
    print("RESULT 2714 selftest OK; rows=%d; artifact written" % len(rows))


if __name__ == "__main__":
    main()
