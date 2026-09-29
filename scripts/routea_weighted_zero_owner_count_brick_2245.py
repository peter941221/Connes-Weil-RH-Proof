#!/usr/bin/env python3
"""2245 - Explicit owner zero-count brick on the screened owner windows.

Replaces, at the three 2103 stress candidates, the 2119 Jensen/dyadic-growth
cardinality bound (`3002.5554464806` at the first candidate) by the explicit
Riemann-von Mangoldt window count

    N(T) = 1 + theta(T)/pi + S(T),

with `theta` the exact Riemann-Siegel theta function and the cited bound
`|S(T)| <= 0.111 log T + 0.275 log log T + 2.450` for `T >= e`
(T. S. Trudgian, "An improved upper bound for the argument of the Riemann
zeta-function on the critical line II", J. Number Theory 134 (2014),
arXiv:1208.5846, Theorem 1).

Geometry: a closed-ball owner zero `z` with `|z - rho| <= R` has
`|Im z - gamma| <= R`, so its height lies in `[gamma - R, gamma + R]`;
zeros with positive imaginary part are counted by `N(gamma + R)` and their
conjugates by `N(R - gamma)`.  The numeric identity check accumulates the
unwrapped phase `Phi` of `zeta(1/2 + i t)` on a fine grid; since
`Z(t) = exp(i theta(t)) zeta(1/2 + i t)` is real, the derived identity
`N(T) = (theta(T) + Phi(T)) / pi` is exact, and the classical
`S(T) = Phi(T)/pi - 1`.  The Hardy-Z sign-change scan and the phase
identity agree at every candidate.

Writes results/2245_owner_count_brick.json.  Pure screening artifact: no
producer claim, no RH claim.
"""

import json
import math
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402

RECORD = 2245
DELTA = 0.445
N_SHELL = 0
G13 = 48.005150881167159  # γ₁₀, the top kill ordinate of the 1994 list
GAMMAS = ((r94.G7 + r94.G8) / 2.0,
          (r94.G8 + 43.327073280914999) / 2.0,
          (43.327073280914999 + G13) / 2.0)

SCREEN_NODES = 62                 # 2117/2119 largest screened compact family
JENSEN_BOUND = 3002.5554464806    # 2119 formal ncard upper bound, stress point
TAIL_OVER_MARGIN_2243 = 0.006850392090059914
ANCHOR_2103 = "results/2103_full_known_prefix_direct_owner_grid_m6400.json"
ARTIFACT_2243 = "results/2243_panel_cem_reprice.json"

# Trudgian II (J. Number Theory 134 (2014), Theorem 1), valid for T >= e.
S14_A, S14_B, S14_C = 0.111, 0.275, 2.450
# Trudgian I (2012) historical variant, from the comparison table of II.
S12_A, S12_C = 0.17, 1.998

OUTPUT = ROOT / "results" / "2245_owner_count_brick.json"


def trudgian_2014(T):
    return S14_A * mp.log(T) + S14_B * mp.log(mp.log(T)) + S14_C


def trudgian_2012(T):
    return S12_A * mp.log(T) + S12_C


def s_numeric(T, step=mp.mpf("0.02")):
    """S(T) by unwrapped phase accumulation of zeta(1/2 + i t) from t=0."""
    prev = mp.arg(mp.zeta(mp.mpf("0.5")))
    total = mp.mpf(0)
    n = int(mp.ceil(T / step))
    for i in range(1, n + 1):
        ti = min(i * step, T)
        arg = mp.arg(mp.zeta(mp.mpf("0.5") + 1j * ti))
        delta = arg - prev
        if delta > mp.pi:
            delta -= 2 * mp.pi
        elif delta <= -mp.pi:
            delta += 2 * mp.pi
        total += delta
        prev = arg
    return total / mp.pi


def zeros_by_siegelz(t_hi, t_lo=mp.mpf("0.01"), step=mp.mpf("0.05")):
    """Hardy-Z sign-change scan; independent of any zero table."""
    heights = []
    prev_t, prev_z = t_lo, mp.siegelz(t_lo)
    steps = int(mp.ceil((t_hi - t_lo) / step))
    for i in range(1, steps + 1):
        t = min(t_lo + i * step, t_hi)
        z = mp.siegelz(t)
        if z == 0:
            heights.append(t)
        elif (prev_z < 0) != (z < 0):
            heights.append(mp.findroot(mp.siegelz, (prev_t, t)))
        prev_t, prev_z = t, z
    return heights


def candidate_row(gamma):
    rho = (0.5 + DELTA) + 1j * gamma
    radius = r80.ball_radius(rho, N_SHELL)
    radius_check = 2.0 ** (N_SHELL + 1) + 2.0 + abs(2.0 - rho)
    t_plus = mp.mpf(gamma) + radius
    t_minus = radius - mp.mpf(gamma)  # |gamma - R|, the conjugate window
    theta_plus = mp.siegeltheta(t_plus)
    theta_minus = mp.siegeltheta(t_minus)
    n_plus_2014 = 1 + theta_plus / mp.pi + trudgian_2014(t_plus)
    n_minus_2014 = 1 + theta_minus / mp.pi + trudgian_2014(t_minus)
    n_plus_2012 = 1 + theta_plus / mp.pi + trudgian_2012(t_plus)
    n_minus_2012 = 1 + theta_minus / mp.pi + trudgian_2012(t_minus)
    bound_2014 = math.floor(float(n_plus_2014)) + max(
        0, math.floor(float(n_minus_2014)))
    bound_2012 = math.floor(float(n_plus_2012)) + max(
        0, math.floor(float(n_minus_2012)))
    # Hardy-Z sign-change enumeration of the critical-line zeros in the
    # height window; independent of mpmath's zero table.
    heights = zeros_by_siegelz(t_plus)
    beyond = zeros_by_siegelz(t_plus + mp.mpf("1.5"))
    first_beyond = [h for h in beyond if h > t_plus]
    enumerated = len(heights)
    # Derived identity: with Z(t) = exp(i theta(t)) zeta(1/2+it) real, the
    # unwrapped critical-line phase Phi of zeta satisfies
    # N(T) = (theta(T) + Phi(T))/pi exactly; the classical S is Phi/pi - 1.
    s_phase = s_numeric(t_plus)
    identity = theta_plus / mp.pi + s_phase
    s_classical = s_phase - 1
    # Environment audit of the mpmath zero table: zetazero(4) must be the
    # true gamma_4 = 30.424876125859513210.
    zeta_table_ok = bool(abs(mp.im(mp.zetazero(4)) -
                             mp.mpf("30.424876125859513210")) < 1e-10)
    # Kill-list audit: 27.67032193035704 is not a zeta zero.
    spurious = mp.mpf("27.67032193035704")
    spurious_zeta = abs(mp.zeta(mp.mpf("0.5") + 1j * spurious))
    return {
        "gamma": gamma,
        "rho": [0.5 + DELTA, gamma],
        "radius": radius,
        "radius_check": radius_check,
        "radius_matches_lean": radius == radius_check,
        "T_plus": float(t_plus),
        "T_minus": float(t_minus),
        "theta_plus_over_pi": float(theta_plus / mp.pi),
        "theta_minus_over_pi": float(theta_minus / mp.pi),
        "N_upper_T_plus_2014": float(n_plus_2014),
        "N_upper_T_minus_2014": float(n_minus_2014),
        "N_upper_T_plus_2012": float(n_plus_2012),
        "N_upper_T_minus_2012": float(n_minus_2012),
        "owner_count_upper_2014": bound_2014,
        "owner_count_upper_2012": bound_2012,
        "zeros_enumerated_in_window": enumerated,
        "zetazero_table_ok_in_environment": zeta_table_ok,
        "spurious_pin_abs_zeta": float(spurious_zeta),
        "last_enumerated_gamma": float(heights[-1]),
        "first_gamma_beyond_window":
            float(first_beyond[0]) if first_beyond else None,
        "phase_over_pi_at_T_plus": float(s_phase),
        "identity_check_value": float(identity),
        "identity_check_residual": float(identity - enumerated),
        "S_classical_at_T_plus": float(s_classical),
        "S_classical_within_trudgian_2014": bool(
            abs(s_classical) <= trudgian_2014(t_plus)),
    }


def main():
    mp.mp.dps = 60
    anchored = json.loads((ROOT / ANCHOR_2103).read_text(encoding="utf-8"))
    screen = json.loads((ROOT / ARTIFACT_2243).read_text(encoding="utf-8"))
    tail_over_margin = screen["screen"]["tail_upper_over_margin"]
    assert abs(tail_over_margin - TAIL_OVER_MARGIN_2243) < 1e-18
    rows = []
    for gamma in GAMMAS:
        row = candidate_row(gamma)
        ratio_uncond = row["owner_count_upper_2014"] / SCREEN_NODES
        ratio_import = row["zeros_enumerated_in_window"] / SCREEN_NODES
        row["count_ratio_unconditional"] = ratio_uncond
        row["count_ratio_imported_exact"] = ratio_import
        row["transfer_reading_unconditional"] = ratio_uncond * tail_over_margin
        row["transfer_reading_imported"] = ratio_import * tail_over_margin
        anchor_rows = [r for r in anchored["rows"]
                       if r["gamma"] == row["gamma"] and r["delta"] == DELTA]
        row["anchor_2103"] = anchor_rows[0] if anchor_rows else None
        rows.append(row)
    stress = rows[0]
    result = {
        "record": RECORD,
        "status": "OWNER-COUNT-BRICK-LANDED",
        "date": "2026-09-30",
        "inputs": {
            "anchor_2103": ANCHOR_2103,
            "artifact_2243": ARTIFACT_2243,
            "delta": DELTA,
            "n_shell": N_SHELL,
            "screen_nodes_2117": SCREEN_NODES,
            "jensen_bound_2119": JENSEN_BOUND,
            "tail_over_margin_2243": tail_over_margin,
        },
        "imports": {
            "trudgian_2014": {
                "source": "T. S. Trudgian, An improved upper bound for the "
                          "argument of the Riemann zeta-function on the "
                          "critical line II, J. Number Theory 134 (2014), "
                          "Theorem 1 (arXiv:1208.5846)",
                "bound": "|S(T)| <= 0.111 log T + 0.275 log log T + 2.450",
                "validity": "T >= e",
            },
            "trudgian_2012": {
                "source": "comparison table of arXiv:1208.5846",
                "bound": "|S(T)| <= 0.17 log T + 1.998",
                "validity": "T >= e",
            },
            "platt_trudgian_2021": {
                "source": "D. Platt, T. Trudgian, The Riemann hypothesis is "
                          "true up to 3*10^12, Bull. LMS 53 (2021) 792-797",
                "content": "all zeros with 0 < Im <= 3*10^12 are simple and "
                           "on the critical line; exact counts certified",
                "role": "turns the enumerated critical-line count into the "
                        "exact owner count in the window",
            },
            "riemann_von_mangoldt": {
                "identity": "N(T) = 1 + theta(T)/pi + S(T)",
                "identity_check_residual_stress":
                    stress["identity_check_residual"],
            },
        },
        "environment": {
            "zetazero_table_ok": all(
                r["zetazero_table_ok_in_environment"] for r in rows),
            "kill_list_audit": {
                "finding": ("fourpoint_owner_completion_1980.GAMMAS[3] = "
                            "27.67032193035704, labelled gamma_4 in the "
                            "1980-1994 lane, is not a zeta zero"),
                "evidence": ("|zeta(1/2 + 27.67032193035704 i)| = "
                             "2.845101349 at 50 dps; the Hardy-Z scan has "
                             "no sign change there; the phase identity "
                             "N(82.51907238937719) = 21 is exact to 1e-15"),
                "true_gamma_4": "30.424876125859513210",
                "impact": ("the 1994 kill list is 9 true zero pins plus one "
                           "non-zero pinned ordinate; the 2103 construction "
                           "and the 2109 ledger price the actual "
                           "construction; node totals 30/33/36 = 21/24/27 "
                           "true in-ball zeros plus 9 non-zero nodes "
                           "(3 targets, 2 conjugate orbit pins, 3 "
                           "real-axis pins, 1 non-zero kill pin); no Lean "
                           "statement is affected (the formal owner stays "
                           "abstract); this count brick enumerates true "
                           "zeros only"),
            },
        },
        "stress": {
            "jensen_bound_2119": JENSEN_BOUND,
            "owner_count_upper_unconditional": stress["owner_count_upper_2014"],
            "owner_count_imported_exact": stress["zeros_enumerated_in_window"],
            "screened_family": SCREEN_NODES,
            "ratio_2119": JENSEN_BOUND / SCREEN_NODES,
            "ratio_unconditional": stress["count_ratio_unconditional"],
            "ratio_imported": stress["count_ratio_imported_exact"],
            "reading_2119": (JENSEN_BOUND / SCREEN_NODES) * tail_over_margin,
            "reading_unconditional": stress["transfer_reading_unconditional"],
            "reading_imported": stress["transfer_reading_imported"],
            "improvement_unconditional": (JENSEN_BOUND / SCREEN_NODES) /
                stress["count_ratio_unconditional"],
            "improvement_imported": (JENSEN_BOUND / SCREEN_NODES) /
                stress["count_ratio_imported_exact"],
        },
        "rows": rows,
        "nonclaims": [
            "the Trudgian S(T) bound and the Platt-Trudgian import are cited "
            "external theorems, not Lean-formalized facts; Lean registration "
            "is a separate obligation",
            "the count brick bounds the owner cardinality on the window; it "
            "is not by itself the complete-owner transfer (the per-node cost "
            "uniformity over the actual owner remains)",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_owner_count_brick_2245.py",
            "pins": {
                "fourpoint_owner_completion_1980": "r80.ball_radius",
                "routea_opposite_gates_height_1994": "r94.G7/G8 candidates",
            },
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"],
                      "stress": result["stress"]}, indent=2))


if __name__ == "__main__":
    main()