#!/usr/bin/env python3
"""2250 - Per-node count uniformity of the 2245 count brick.

Extends the 2245 owner-count brick (three stress candidates) to every node
of the 2103 direct known-prefix construction (30 nodes at the candidate
`rho = 0.945 + 39.25244858548658 i`).  For each node the family window in
the height variable is `[||h| - a|, |h| + a]` with `h` the node height and
`a = SCALE * width` the family support half-width from the 2103 width
plan (mirrored to `|h|`, since conjugation maps a negative-height family
window onto the same positive ordinates); the unconditional count is
window-framed as `(theta(T+) - theta(T-))/pi + S_up(T+) + S_up(T-)` and
the Hardy-Z scan gives the exact window count, with the worst-node
constants registered.  The global owner window (the closed-ball window of
2245) is recomputed for consistency and asserted against the committed
2245 values.

Boundary rules (exact, not bounds): no zero has height below the first
ordinate `gamma_1 = 14.134725141734693790`, so windows with `T+ < gamma_1`
count zero unconditionally; Trudgian's `|S(T)|` bound is used only for
`T >= e`, where it is valid.

Scope: the count side per node.  The charge side of the complete-owner
transfer (per-node charge <= uniform per-node budget `tail/62`) is NOT
touched; it stays open and is stated in the record.

Writes results/2250_pernode_count_uniformity.json.  Pure screening
artifact: no producer claim, no RH claim.
"""

import json
import math
import sys
import time
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80      # noqa: E402
import fourpoint_offline_owner_1981 as r81         # noqa: E402
import routea_opposite_gates_height_1994 as r94    # noqa: E402
import routea_weighted_zero_owner_count_brick_2245 as r45  # noqa: E402

RECORD = 2250
GAMMA = 39.25244858548658
DELTA = 0.445
SCALE = 0.80
N_SHELL = 0
SCREEN_NODES = 62
TAIL_OVER_MARGIN_2248 = 0.0029211540846331738
GAMMA_1 = mp.mpf("14.134725141734693790")
E_CONST = mp.mpf("2.718281828459045235")

OUTPUT = ROOT / "results" / "2250_pernode_count_uniformity.json"


def build_nodes():
    """The exact 2103 construction node list with family widths."""
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes = r94.owner_nodes_ext(rho, GAMMA)[0]
    radius = r80.ball_radius(rho, N_SHELL)
    mp.mp.dps = 50
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(
                abs(z - existing) > 1e-6 for existing in nodes):
            nodes.append(z)
    plan = {"main": 0, "real": 0}
    rows = []
    for index, z in enumerate(nodes):
        height = float(z.imag)
        if abs(abs(height) - GAMMA) < 1e-9:
            width = r81.WIDTHS_H1[plan["main"]]
            plan["main"] += 1
        elif abs(height) < 1e-9:
            width = r81.WIDTHS_REAL[plan["real"]]
            plan["real"] += 1
        else:
            width = 2.2
        rows.append({
            "index": index,
            "re": float(z.real), "im": float(z.imag),
            "height": height, "width": width,
            "a": SCALE * width,
        })
    return rho, radius, rows


def window_count(t_plus, t_minus):
    """Unconditional upper bound for the number of zeros with height in
    [t_minus, t_plus], window-framed:

        count = N(t_plus) - N(t_minus)
              <= (theta(t_plus)/pi + S_up(t_plus))
                 - (theta(t_minus)/pi - S_up(t_minus))

    with `S_up = trudgian_2014` valid for T >= e.  Below the first
    ordinate `gamma_1` no zero exists (exact), so the t_minus side
    contributes nothing when `t_minus < gamma_1`.
    """
    t_plus_mp = mp.mpf(t_plus)
    t_minus_mp = mp.mpf(t_minus)
    if t_plus_mp < GAMMA_1:
        return 0, None, None, None
    theta_plus = mp.siegeltheta(t_plus_mp)
    s_up_plus = r45.trudgian_2014(t_plus_mp)
    if t_minus_mp < GAMMA_1:
        upper = 1 + theta_plus / mp.pi + s_up_plus
        return (math.floor(float(upper) + 1e-9), theta_plus, s_up_plus, None)
    assert t_minus_mp >= E_CONST
    theta_minus = mp.siegeltheta(t_minus_mp)
    s_up_minus = r45.trudgian_2014(t_minus_mp)
    upper = ((theta_plus - theta_minus) / mp.pi
             + s_up_plus + s_up_minus)
    return (math.floor(float(upper) + 1e-9), theta_plus, s_up_plus,
            float(theta_minus))


def main():
    mp.mp.dps = 60
    t_start = time.time()
    _, _, rows = build_nodes()
    # one Hardy-Z scan covering every window and one ordinate beyond
    t_max = max(mp.mpf(row["height"]) + mp.mpf(row["a"]) for row in rows)
    scan_hi = t_max + mp.mpf("1.5")
    heights = r45.zeros_by_siegelz(scan_hi)
    # phase identity check at the largest window edge
    s_phase = r45.s_numeric(t_max)
    theta_max = mp.siegeltheta(t_max)
    identity_residual = float(
        theta_max / mp.pi + s_phase - len([h for h in heights if h <= t_max]))

    per_node = []
    for row in rows:
        height_abs = abs(mp.mpf(row["height"]))
        t_plus = height_abs + mp.mpf(row["a"])
        t_minus = max(mp.mpf(0), height_abs - mp.mpf(row["a"]))
        bound, theta_plus, s_up_plus, theta_minus = window_count(t_plus, t_minus)
        within = [h for h in heights if h <= t_plus]
        below = [h for h in heights if h <= t_minus]
        beyond = [h for h in heights if h > t_plus]
        per_node.append({
            "node": row["index"],
            "height": row["height"], "a": row["a"],
            "T_plus": float(t_plus), "T_minus": float(t_minus),
            "theta_plus_over_pi":
                float(theta_plus / mp.pi) if theta_plus is not None else None,
            "S_upper_2014": float(s_up_plus) if s_up_plus is not None
            else None,
            "theta_minus_over_pi": float(theta_minus / mp.pi)
            if theta_minus is not None else None,
            "count_window_upper_2014": bound,
            "zeros_in_window_enumerated": len(within) - len(below),
            "last_ordinate_at_or_below_T_plus":
                float(within[-1]) if within else None,
            "first_ordinate_above_T_plus":
                float(beyond[0]) if beyond else None,
            "ratio_unconditional": bound / SCREEN_NODES,
            "ratio_imported": (len(within) - len(below)) / SCREEN_NODES,
            "reading_unconditional": (bound / SCREEN_NODES)
                * TAIL_OVER_MARGIN_2248,
            "reading_imported": ((len(within) - len(below)) / SCREEN_NODES)
                * TAIL_OVER_MARGIN_2248,
        })
    worst_bound = max(row["count_window_upper_2014"] for row in per_node)
    worst_enum = max(row["zeros_in_window_enumerated"] for row in per_node)
    # global owner window: the 2245 closed-ball window, recomputed
    ball = r45.candidate_row(GAMMA)
    brick = json.loads(
        (ROOT / "results" / "2245_owner_count_brick.json")
        .read_text(encoding="utf-8"))
    stress = brick["stress"]
    ball_consistent = (
        ball["owner_count_upper_2014"] == stress["owner_count_upper_unconditional"]
        and ball["zeros_enumerated_in_window"]
        == stress["owner_count_imported_exact"])
    result = {
        "record": RECORD,
        "status": "PERNODE-COUNT-UNIFORMITY-SCREEN",
        "date": "2026-09-30",
        "inputs": {
            "candidate": {"rho": [0.5 + DELTA, GAMMA], "delta": DELTA,
                          "scale": SCALE, "n_shell": N_SHELL},
            "screen_nodes_2117": SCREEN_NODES,
            "tail_over_margin_2248": TAIL_OVER_MARGIN_2248,
            "gamma_1": str(GAMMA_1),
        },
        "scan": {
            "t_max_plus_margin": float(scan_hi),
            "ordinates_found": len(heights),
            "identity_check_at_T": float(t_max),
            "identity_check_residual": identity_residual,
            "scan_seconds": time.time() - t_start,
        },
        "ball_window_2245": {
            "T_plus": ball["T_plus"], "T_minus": ball["T_minus"],
            "owner_count_upper_2014": ball["owner_count_upper_2014"],
            "zeros_enumerated": ball["zeros_enumerated_in_window"],
            "consistent_with_committed_2245": ball_consistent,
        },
        "worst_node": {
            "count_upper_2014": worst_bound,
            "zeros_enumerated": worst_enum,
            "ratio_unconditional": worst_bound / SCREEN_NODES,
            "ratio_imported": worst_enum / SCREEN_NODES,
            "reading_unconditional": (worst_bound / SCREEN_NODES)
                * TAIL_OVER_MARGIN_2248,
            "reading_imported": (worst_enum / SCREEN_NODES)
                * TAIL_OVER_MARGIN_2248,
            "uniformity_holds_unconditional": worst_bound
                <= stress["owner_count_upper_unconditional"],
            "uniformity_holds_imported": worst_enum
                <= stress["owner_count_imported_exact"],
        },
        "rows": per_node,
        "nonclaims": [
            "count side only: the per-node charge uniformity of the "
            "complete-owner transfer (per-node charge <= tail/62) is NOT "
            "established here; the transferred-charge product remains a "
            "reading",
            "the family window [||h| - a|, |h| + a] is the height reach of "
            "the node's own interpolation family; it is not an owner "
            "membership statement",
            "the Trudgian S(T) bound and the Platt-Trudgian import are "
            "cited external theorems; Lean registration is separate",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_pernode_count_2250.py",
            "machinery": "scripts/routea_weighted_zero_owner_count_brick_2245.py",
            "pins": {
                "fourpoint_owner_completion_1980": "r80.ball_radius",
                "fourpoint_offline_owner_1981": "r81.WIDTHS_H1/WIDTHS_REAL",
                "routea_opposite_gates_height_1994": "r94.owner_nodes_ext",
            },
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"],
                      "scan": result["scan"],
                      "ball_window_2245": result["ball_window_2245"],
                      "worst_node": result["worst_node"]}, indent=2))


if __name__ == "__main__":
    main()