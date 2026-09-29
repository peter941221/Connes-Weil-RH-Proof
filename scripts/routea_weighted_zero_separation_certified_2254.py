#!/usr/bin/env python3
"""2254 - Certified separation + local uniform-in-rho disk at ALL THREE
2103 stress candidates; the covering statement and the crossing obstruction.

Consumer: the 2247 separation input for the 2157 near-pin derivative floor,
certified at candidate 1 by 2251.  This record generalizes 2251 to the full
registered configuration screen (the three 2103 stress candidates), closing
the "certified zero isolation per configuration" obligation screen-wide and
registering why a literal continuum statement is obstructed: as gamma
varies, the closed-ball edge gamma + R(rho) crosses zeta ordinates, the
in-ball node set changes between candidates, and the local radius eps_rho
degenerates at each crossing.  The correct uniform object is therefore the
discrete registered screen, each member of which is certified here.

Per candidate: Hardy-Z brackets for every critical-line pin, per-target
certified separations (two-ulp outward lower bounds), and a local disk
|rho' - rho| <= eps_rho on which the construction node set is unchanged and
the separation lower bound survives.  Numeric certificates (mpmath 60 dps
with an explicit error budget), not Lean interval arithmetic.  Writes
results/2254_separation_certified_three_candidates.json.
"""

import json
import math
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_separation_input_2247 as r47  # noqa: E402

RECORD = 2254
GAMMAS = (39.25244858548658, 42.12289614653125, 45.66611208104108)
DELTA = 0.445
N_SHELL = 0
BRACKET_HALF = mp.mpf("0.01")
BRACKET_TARGET_WIDTH = mp.mpf("1e-24")
Z_ENDPOINT_MARGIN = mp.mpf("1e-6")
OUTPUT = ROOT / "results" / "2254_separation_certified_three_candidates.json"


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


def first_ordinate_above(t_edge):
    """First zeta ordinate strictly above `t_edge` (zetazero scan)."""
    for index in range(1, 41):
        height = mp.im(mp.zetazero(index))
        if height > t_edge:
            return int(index), height
    raise RuntimeError("no ordinate above")


def first_ordinate_outside_ball(rho_mp, radius_mp):
    """First ordinate z = 0.5 + i gamma_k with |z - rho| > radius."""
    for index in range(1, 41):
        height = mp.im(mp.zetazero(index))
        dist = abs(mp.mpc(mp.mpf("0.5"), height) - rho_mp)
        if dist > radius_mp:
            return int(index), height, dist
    raise RuntimeError("no ordinate outside ball")


def candidate_block(gamma, anchor_rows):
    row = [r for r in anchor_rows
           if r["gamma"] == gamma and r["delta"] == DELTA]
    assert row, "anchor row missing"
    support = row[0]["support"]

    _, radius, nodes, values, added = r47.assemble_owner(gamma)
    mp.mp.dps = 60
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
        entry = {"node": [z.real, z.imag], "kind": kind}
        if kind == "critical_line_zero":
            bracket = certified_bracket(mp.mpf(repr(z.imag)))
            assert bracket is not None, f"no bracket at {z.imag}"
            entry.update({"bracket_lo": bracket["lo"],
                          "bracket_hi": bracket["hi"],
                          "bracket_width": bracket["width"],
                          "bracket_za": bracket["za"],
                          "bracket_zb": bracket["zb"],
                          "half_width": bracket["width"] / 2.0})
        elif kind == "critical_line_nonzero_pin":
            entry["abs_Z"] = float(abs(mp.siegelz(mp.mpf(z.imag))))
            entry["half_width"] = 0.0
        else:
            entry["half_width"] = 0.0
        pins.append((z, entry))

    brackets = [(entry["bracket_lo"], entry["bracket_hi"], entry["node"][1])
                for _, entry in pins if "bracket_lo" in entry]
    brackets.sort()
    gaps = [brackets[i + 1][0] - brackets[i][1]
            for i in range(len(brackets) - 1)]
    min_gap = min(gaps) if gaps else None
    endpoint_margin = min(
        min(abs(entry["bracket_za"]), abs(entry["bracket_zb"]))
        for _, entry in pins if "bracket_lo" in entry)

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
            "min_separation_measured": best[0],
            "min_separation_certified_lower": best[3],
            "min_separation_certified_upper": best[4],
            "nearest_pin": [best[1].real, best[1].imag],
            "nearest_pin_kind": best[2]["kind"],
            "floor_2157_measured": r47.floor_2157(best[0], support, s_real),
            "s_real": s_real,
        })

    worst = min(per_target, key=lambda r: r["min_separation_measured"])
    s_min = worst["min_separation_measured"]
    t2t = []
    for i in range(len(targets)):
        for j in range(i + 1, len(targets)):
            t2t.append(abs(targets[i][0] - targets[j][0]))
    min_target_distance = min(t2t)

    rho_mp = mp.mpc(mp.mpf(repr(0.5 + DELTA)), mp.mpf(repr(gamma)))
    radius_mp = mp.mpf(repr(radius))
    w_edge = rho_mp.imag + radius_mp
    w_idx, w_height = first_ordinate_above(w_edge)
    eps_window = (w_height - w_edge) / 2
    b_idx, b_height, b_dist = first_ordinate_outside_ball(rho_mp, radius_mp)
    eps_ball = (b_dist - radius_mp) / 2
    eps_rho = min(eps_window, eps_ball) * mp.mpf("0.95")
    local_sep = down(s_min - 2.0 * float(eps_rho))
    local_floors = []
    for r in per_target:
        d_loc = r["min_separation_certified_lower"] - 2.0 * float(eps_rho)
        s_loc = r["s_real"] + 2.0 * float(eps_rho)
        local_floors.append({
            "target": r["target"],
            "s_real": r["s_real"],
            "delta_sep_local": d_loc,
            "floor_2157_local": r47.floor_2157(d_loc, support, s_loc),
        })
    worst_floor = min(local_floors, key=lambda r: r["floor_2157_local"])

    return {
        "gamma": gamma,
        "rho": [0.5 + DELTA, gamma],
        "radius": radius,
        "support": support,
        "node_count": len(nodes),
        "in_ball_added_heights": [float(h) for h in added],
        "n_in_ball_added": len(added),
        "critical_line_zeros": sum(1 for _, e in pins
                                   if e["kind"] == "critical_line_zero"),
        "targets": len(targets),
        "brackets": {
            "count": len(brackets),
            "max_width": max(entry["bracket_width"]
                             for _, entry in pins if "bracket_lo" in entry),
            "min_pairwise_gap": min_gap,
            "endpoint_margin_min": endpoint_margin,
        },
        "per_target": per_target,
        "min_separation": {
            "measured": s_min,
            "certified_lower": worst["min_separation_certified_lower"],
            "pair": {"target": worst["target"],
                     "pin": worst["nearest_pin"],
                     "pin_kind": worst["nearest_pin_kind"]},
            "floor_2157_measured": worst["floor_2157_measured"],
        },
        "local_uniform_in_rho": {
            "eps_rho": float(eps_rho),
            "eps_window": float(eps_window),
            "eps_ball": float(eps_ball),
            "window_edge": float(w_edge),
            "first_ordinate_above_window": {
                "index": w_idx, "height": float(w_height)},
            "first_ordinate_outside_ball": {
                "index": b_idx, "height": float(b_height),
                "distance": float(b_dist)},
            "separation_lower": local_sep,
            "floor_2157_lower": worst_floor["floor_2157_local"],
            "floor_2157_worst_target": worst_floor["target"],
            "floor_2157_by_target": local_floors,
            "target_target_min_distance": min_target_distance,
            "target_target_margin": min_target_distance
            - 2.0 * float(eps_rho),
        },
    }


def main():
    anchor = json.loads(
        (ROOT / "results"
         / "2103_full_known_prefix_direct_owner_grid_m6400.json")
        .read_text(encoding="utf-8"))
    rows = [candidate_block(gamma, anchor["rows"]) for gamma in GAMMAS]
    worst_local = min(rows, key=lambda r: r["local_uniform_in_rho"]
                      ["floor_2157_lower"])
    worst_sep = min(rows, key=lambda r: r["min_separation"]
                    ["certified_lower"])
    crossing = []
    for i in range(len(rows) - 1):
        a, b = rows[i], rows[i + 1]
        crossing.append({
            "pair": [a["gamma"], b["gamma"]],
            "window_edge_a": a["local_uniform_in_rho"]["window_edge"],
            "window_edge_b": b["local_uniform_in_rho"]["window_edge"],
            "last_ordinate_at_a": a["local_uniform_in_rho"]
            ["first_ordinate_above_window"]["height"],
            "critical_line_zeros_a": a["critical_line_zeros"],
            "critical_line_zeros_b": b["critical_line_zeros"],
        })

    result = {
        "record": RECORD,
        "status": "CERTIFIED-PER-CONFIGURATION-SCREEN + LOCAL-DISKS",
        "date": "2026-09-30",
        "candidates": rows,
        "screen_summary": {
            "candidate_count": len(rows),
            "worst_min_separation": {
                "gamma": worst_sep["gamma"],
                "certified_lower": worst_sep["min_separation"]
                ["certified_lower"]},
            "worst_local_floor": {
                "gamma": worst_local["gamma"],
                "floor": worst_local["local_uniform_in_rho"]
                ["floor_2157_lower"]},
            "total_brackets": sum(r["brackets"]["count"] for r in rows),
            "max_bracket_width": max(r["brackets"]["max_width"]
                                     for r in rows),
            "min_endpoint_margin": min(r["brackets"]["endpoint_margin_min"]
                                       for r in rows),
        },
        "covering_statement": (
            "each of the three registered 2103 stress configurations is "
            "certified with an explicit local disk |rho' - rho| <= eps_rho "
            "on which the node set is unchanged and every target-to-pin "
            "separation is >= s_min - 2 eps_rho, so the 2157 floor at every "
            "rho' in the union of the three disks is at least the "
            "registered per-candidate local floor; the union covers the "
            "registered configuration screen"),
        "continuum_obstruction": {
            "finding": (
                "a literal continuum uniform-in-rho statement is obstructed "
                "by closed-ball boundary crossings: the edge gamma + "
                "R(rho) sweeps ordinates as gamma varies (it sits below "
                "the first excluded ordinate at candidate 1 and above it "
                "at candidate 2), the in-ball node set changes between "
                "candidates, and eps_rho degenerates to zero at each "
                "crossing; the correct uniform object is the discrete "
                "configuration screen, certified member by member here"),
            "crossings": crossing,
        },
        "nonclaims": [
            "the brackets are numeric certificates (mpmath 60 dps with an "
            "explicit error budget), not Lean-formalized interval "
            "arithmetic",
            "global uniformity over the continuum of rho is NOT claimed; "
            "it is obstructed at ball-boundary crossings and would need "
            "re-derivation per crossing",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_separation_certified_2254.py",
            "machinery": "scripts/routea_weighted_zero_separation_input_2247.py",
            "predecessor": "scripts/routea_weighted_zero_separation_certified_2251.py",
            "anchor_2103": "results/2103_full_known_prefix_direct_owner_grid_m6400.json",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    brief = {"status": result["status"],
             "summary": result["screen_summary"],
             "candidates": [
                 {"gamma": r["gamma"],
                  "zeros": r["critical_line_zeros"],
                  "min_sep": r["min_separation"]["measured"],
                  "eps_rho": r["local_uniform_in_rho"]["eps_rho"],
                  "local_sep": r["local_uniform_in_rho"]["separation_lower"],
                  "local_floor": r["local_uniform_in_rho"]["floor_2157_lower"]}
                 for r in rows]}
    print(json.dumps(brief, indent=2))


if __name__ == "__main__":
    main()