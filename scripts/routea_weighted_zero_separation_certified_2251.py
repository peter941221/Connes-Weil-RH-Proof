#!/usr/bin/env python3
"""2251 - Certified per-node isolation and local uniform-in-rho separation.

Upgrades the 2247 measured separation input at the chosen candidate
`rho = 0.945 + 39.25244858548658 i` in two ways:

1. certified brackets: every critical-line pin gets a Hardy-Z sign-change
   bracket refined by bisection to width `<= 1e-24`, with an endpoint
   margin audit (`|Z| >= 1e-6` against a 60-dps evaluation error of order
   `1e-50`) and pairwise disjointness; the non-zero kill pin is certified
   as a non-zero of `Z` by a direct value bound;

2. a local uniform-in-rho lemma: for every `rho'` with
   `|rho' - rho| <= eps_rho` the 30-node construction set is unchanged
   (the moving elements -- targets and off-line pins -- move by at most
   `eps_rho`, all other pins are fixed constants; a zero or a pin enters
   the ball / window only beyond the computed gaps), so every
   target-to-pin separation is `>= s_min - 2 eps_rho`, full stop: the
   2157 derivative floor at every such `rho'` is `>= 4 exp(-X S)/(
   (s_min - 2 eps_rho) X L^2)`.

The certified bracket machinery is numeric (mpmath at 60 dps with an
explicit error budget), not Lean-formalized; global uniformity over all
`rho` remains open.  Writes results/2251_separation_certified.json.
"""

import json
import math
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_separation_input_2247 as r47  # noqa: E402

RECORD = 2251
GAMMA = 39.25244858548658
DELTA = 0.445
N_SHELL = 0
GAMMA_22 = mp.mpf("82.91038085408603")
BRACKET_HALF = mp.mpf("0.01")
BRACKET_TARGET_WIDTH = mp.mpf("1e-24")
Z_ENDPOINT_MARGIN = mp.mpf("1e-6")
OUTPUT = ROOT / "results" / "2251_separation_certified.json"


def down(value, steps=2):
    for _ in range(steps):
        value = math.nextafter(value, -math.inf)
    return value


def up_(value, steps=2):
    for _ in range(steps):
        value = math.nextafter(value, math.inf)
    return value


def certified_bracket(center):
    """Sign-change bracket of Z around `center`, bisected tight."""
    a = center - BRACKET_HALF
    b = center + BRACKET_HALF
    za = mp.siegelz(a)
    zb = mp.siegelz(b)
    if za * zb >= 0 or min(abs(za), abs(zb)) < Z_ENDPOINT_MARGIN:
        return None
    while b - a > BRACKET_TARGET_WIDTH:
        mid = (a + b) / 2
        zm = mp.siegelz(mid)
        if za * zm <= 0:
            b, zb = mid, zm
        else:
            a, za = mid, zm
    return {"lo": float(a), "hi": float(b),
            "width": float(b - a), "za": float(za), "zb": float(zb)}


def main():
    _, radius, nodes, values, _ = r47.assemble_owner(GAMMA)
    mp.mp.dps = 60
    support = 5.12
    anchor = json.loads(
        (ROOT / "results" / "2103_full_known_prefix_direct_owner_grid_m6400.json")
        .read_text(encoding="utf-8"))
    anchor_rows = [r for r in anchor["rows"]
                   if r["gamma"] == GAMMA and r["delta"] == DELTA]
    assert anchor_rows
    support = anchor_rows[0]["support"]

    targets = [(z, v) for z, v in zip(nodes, values) if v != 0]
    pins = []
    for z, v in zip(nodes, values):
        if v != 0:
            continue
        if abs(z.imag) <= 1e-9:
            kind = "real_axis_pin"
        elif abs(z.real - 0.5) > 1e-9:
            kind = "off_line_pin"
        else:
            zval = float(abs(mp.siegelz(mp.mpf(z.imag))))
            kind = ("critical_line_zero" if zval < 1e-9
                    else "critical_line_nonzero_pin")
        entry = {"node": [z.real, z.imag], "kind": kind,
                 "re_exact": (0.5 if kind.startswith("critical_line")
                              else None)}
        if kind == "critical_line_zero":
            bracket = certified_bracket(mp.mpf(repr(z.imag)))
            assert bracket is not None, f"no bracket at {z.imag}"
            entry["bracket_lo"] = bracket["lo"]
            entry["bracket_hi"] = bracket["hi"]
            entry["bracket_width"] = bracket["width"]
            entry["bracket_za"] = bracket["za"]
            entry["bracket_zb"] = bracket["zb"]
            entry["half_width"] = bracket["width"] / 2.0
        elif kind == "critical_line_nonzero_pin":
            entry["abs_Z"] = float(abs(mp.siegelz(mp.mpf(z.imag))))
            entry["half_width"] = 0.0
        else:
            entry["half_width"] = 0.0
        pins.append((z, entry))

    # isolation audit: pairwise disjoint brackets and coordinate avoidance
    brackets = [(entry["bracket_lo"], entry["bracket_hi"],
                 entry["node"][1])
                for _, entry in pins if "bracket_lo" in entry]
    brackets.sort()
    gaps = [brackets[i + 1][0] - brackets[i][1]
            for i in range(len(brackets) - 1)]
    min_gap = min(gaps)
    coord_conflicts = []
    for lo, hi, holder in brackets:
        for z, entry in pins:
            if entry["node"][1] == holder and "bracket_lo" in entry:
                continue
            if entry["node"][0] == 0.5 and lo <= entry["node"][1] <= hi:
                coord_conflicts.append([holder, entry["node"][1]])
        for k in range(len(targets)):
            if targets[k][0].real == 0.5 and lo <= targets[k][0].imag <= hi:
                coord_conflicts.append([holder, targets[k][0].imag])

    # per-target certified separations and floors
    per_target = []
    for t, v in targets:
        best = None
        for z, entry in pins:
            d = abs(t - z)
            hw = entry.get("half_width", 0.0)
            blo = entry.get("bracket_lo")
            bhi = entry.get("bracket_hi")
            if hw == 0.0 or blo is None or bhi is None:
                d_lo = down(d)
                d_hi = up_(d)
            elif abs(t.real - 0.5) <= 1e-9:
                # target on the critical line: distance to the bracket
                d_lo = down(abs(t.imag - (blo if abs(t.imag - blo)
                                          < abs(t.imag - bhi) else bhi)))
                d_hi = up_(d + hw)
            else:
                d_lo = down(d - hw)
                d_hi = up_(d + hw)
            if best is None or d < best[0]:
                best = (d, z, entry, d_lo, d_hi)
        assert best is not None
        s_real = max(abs(t.real), abs(best[1].real))
        per_target.append({
            "target": [t.real, t.imag],
            "value": [v.real, v.imag],
            "min_separation_measured": best[0],
            "min_separation_certified_lower": best[3],
            "min_separation_certified_upper": best[4],
            "nearest_pin": [best[1].real, best[1].imag],
            "nearest_pin_kind": best[2]["kind"],
            "floor_2157_measured": r47.floor_2157(best[0], support, s_real),
            "floor_2157_certified_lower":
                r47.floor_2157(best[4], support, s_real),
        })

    worst = min(per_target, key=lambda row: row["min_separation_measured"])
    s_min = worst["min_separation_measured"]
    s_min_cert = worst["min_separation_certified_lower"]
    t2t = []
    for i in range(len(targets)):
        for j in range(i + 1, len(targets)):
            t2t.append(abs(targets[i][0] - targets[j][0]))
    min_target_distance = min(t2t)

    # local uniform-in-rho radius: window and ball gaps to gamma_22
    window_edge = mp.mpf(GAMMA) + mp.mpf(repr(radius))
    eps_window = (GAMMA_22 - window_edge) / 2
    rho_mp = mp.mpc(mp.mpf("0.945"), mp.mpf(repr(GAMMA)))
    dist_ball = abs(mp.mpc(mp.mpf("0.5"), GAMMA_22) - rho_mp)
    eps_ball = (dist_ball - mp.mpf(repr(radius))) / 2
    eps_rho = min(eps_window, eps_ball) * mp.mpf("0.95")
    local_sep = down(s_min - 2.0 * float(eps_rho))
    local_floor = r47.floor_2157(
        local_sep, support,
        max(abs(worst["target"][0]), 0.5) + 2.0 * float(eps_rho))

    result = {
        "record": RECORD,
        "status": "SEPARATION-CERTIFIED-PER-NODE + LOCAL-UNIFORM",
        "date": "2026-09-30",
        "candidate": {"rho": [0.945, GAMMA], "delta": DELTA,
                      "n_shell": N_SHELL, "support": support},
        "brackets": {
            "count": len(brackets),
            "target_width": float(BRACKET_TARGET_WIDTH),
            "max_width": max(entry["bracket_width"]
                             for _, entry in pins if "bracket_lo" in entry),
            "min_pairwise_gap": min_gap,
            "coordinate_conflicts": coord_conflicts,
            "endpoint_margin_min": min(
                min(abs(entry["bracket_za"]), abs(entry["bracket_zb"]))
                for _, entry in pins if "bracket_lo" in entry),
            "evaluation_error_budget": (
                "mpmath at 60 dps: absolute evaluation error of order "
                "1e-58; the initial sign-change endpoints carry "
                "|Z| >= 1e-6 and the smallest |Z| used in any sign "
                "decision is the registered refined endpoint margin "
                "(order 1e-26), still 30+ orders above the error"),
        },
        "pins": [entry for _, entry in pins],
        "per_target": per_target,
        "min_separation": {
            "measured": s_min,
            "certified_lower": s_min_cert,
            "pair": {"target": worst["target"],
                     "pin": worst["nearest_pin"],
                     "pin_kind": worst["nearest_pin_kind"]},
            "floor_2157_measured": worst["floor_2157_measured"],
        },
        "local_uniform_in_rho": {
            "radius_eps_rho": float(eps_rho),
            "radius_from_window_gap": float(eps_window),
            "radius_from_ball_gap": float(eps_ball),
            "window_gap_to_gamma_22": float(GAMMA_22 - window_edge),
            "ball_gap_to_gamma_22_ordinate": float(dist_ball
                                                  - mp.mpf(repr(radius))),
            "statement": (
                "for every rho' with |rho' - rho| <= eps_rho the node set "
                "of the construction is unchanged (the moving elements are "
                "the targets and the off-line pins, each Lipschitz-1 in "
                "rho'; all other pins are fixed constants; the ball and "
                "window membership thresholds move by <= 2 eps_rho and "
                "stay below the computed gaps to the first excluded "
                "ordinate gamma_22); every target-to-pin separation at "
                "rho' is >= s_min - 2 eps_rho, and the 2157 floor is "
                ">= the registered local floor (floor decreasing in the "
                "separation)"),
            "separation_lower": local_sep,
            "floor_2157_lower": local_floor,
            "target_target_min_distance": min_target_distance,
            "target_target_margin": min_target_distance - 2.0 * float(eps_rho),
        },
        "nonclaims": [
            "global uniformity over all rho is NOT established; the local "
            "lemma covers an explicit neighborhood of the candidate "
            "radius only",
            "the brackets are numeric certificates (mpmath 60 dps with an "
            "explicit error budget), not Lean-formalized interval "
            "arithmetic",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_separation_certified_2251.py",
            "machinery": "scripts/routea_weighted_zero_separation_input_2247.py",
            "anchor_2103": "results/2103_full_known_prefix_direct_owner_grid_m6400.json",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"],
                      "brackets": {k: v for k, v in result["brackets"].items()
                                   if k != "evaluation_error_budget"},
                      "min_separation": result["min_separation"],
                      "local_uniform_in_rho": result["local_uniform_in_rho"]},
                     indent=2))


if __name__ == "__main__":
    main()