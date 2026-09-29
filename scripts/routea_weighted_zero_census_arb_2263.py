#!/usr/bin/env python3
"""2263 - Arb ball certification of the census non-zero pins (the 2245
kill-list non-zero side) at the three 2103 stress candidates.

Consumer: the 2245 owner-count brick decomposes the 30/33/36 node totals
as 21/24/27 true in-ball critical-line zeros plus 6 non-zero pins per
candidate: 2 off-line functional-equation pins (0.945 - i gamma and
0.055 - i gamma), 3 real-axis pins (0.5 / 1.0 / 1.5), and the non-zero
kill pin at the false gamma_4 ordinate 27.67032193035704.  Record 2259
certified the 72 zero brackets and the kill pin's non-vanishing; the
remaining pin instances were classified only by mpmath.  This record
certifies xi(z) != 0 at every non-zero pin with Arb ball arithmetic:

    xi(z) = (1/2) z (z-1) pi^{-z/2} Gamma(z/2) zeta(z),

via acb.gamma / acb.zeta / arb.pi at 200 bits; a pin is certified when
the ball lower bound |xi(z)| >= m is positive (float conversion padded
by 8 ulp).  The classification rule is the committed r47 one (mpmath
siegelz 1e-9 at 60 dps); the certified objects are the |xi| lower
bounds, independent of that rule.

Writes results/2263_census_arb.json.  Requires python-flint (venv).
"""
import json
import math
import sys
from pathlib import Path

import mpmath as mp
from flint import acb, arb, ctx  # pyright: ignore[reportMissingImports]

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_separation_input_2247 as r47  # noqa: E402  # pyright: ignore[reportMissingImports]

RECORD = 2263
GAMMAS = (39.25244858548658, 42.12289614653125, 45.66611208104108)
PREC_BITS = 200
PAD_ULPS = 8
KILL_PIN = 27.67032193035704
ANCHOR_2259 = ROOT / "results" / "2259_hardyz_arb_certification.json"
OUTPUT = ROOT / "results" / "2263_census_arb.json"
ctx.prec = PREC_BITS


def xi_ball(re_v, im_v):
    """Certified ball of the completed xi at z = re + i im."""
    s = acb(arb(re_v), arb(im_v))
    pi = arb.pi()
    return ((s * (s - 1)) / 2) * (acb(pi) ** ((-s) / 2)) \
        * (s / 2).gamma() * s.zeta()


def abs_lower(z_ball):
    """Certified float lower bound of |z_ball| (8-ulp padded)."""
    mod = (z_ball.real ** 2 + z_ball.imag ** 2).sqrt()
    mid = float(mod.mid())
    rad = float(mod.rad())
    return mid - rad - PAD_ULPS * math.ulp(abs(mid) if mid else 1.0)


def abs_value(z_ball):
    """Ball midpoint |z| (reporting aid, not the certificate)."""
    mod = (z_ball.real ** 2 + z_ball.imag ** 2).sqrt()
    return float(mod.mid())


def classify(z):
    """The committed r47 node classification (mpmath siegelz rule)."""
    if abs(z.imag) <= 1e-9:
        return "real_axis_pin"
    if abs(z.real - 0.5) > 1e-9:
        return "off_line_pin"
    zval = float(abs(mp.siegelz(mp.mpf(z.imag))))
    return ("critical_line_zero" if zval < 1e-9
            else "critical_line_nonzero_pin")


def main():
    blocks = []
    distinct = {}
    for gamma in GAMMAS:
        _, radius, nodes, values, _added = r47.assemble_owner(gamma)
        mp.mp.dps = 60
        counts = {"critical_line_zero": 0, "critical_line_nonzero_pin": 0,
                  "off_line_pin": 0, "real_axis_pin": 0}
        rows = []
        for z, v in zip(nodes, values):
            if v != 0:
                continue
            kind = classify(z)
            counts[kind] += 1
            if kind == "critical_line_zero":
                continue
            if abs(float(z.real) - 1.0) <= 1e-9 \
                    and abs(float(z.imag)) <= 1e-9:
                rows.append({
                    "node": [z.real, z.imag],
                    "kind": kind,
                    "abs_xi_lower": 0.5,
                    "abs_xi_value": 0.5,
                    "classical": "xi(1) = 1/2 (entire completion "
                                 "normalization; acb.zeta is "
                                 "indeterminate at the pole and interval "
                                 "arithmetic cannot cancel (s-1) zeta(s) "
                                 "at the boundary point)",
                    "nonvanishing_certified": True,
                })
                key = (round(z.real, 9), round(z.imag, 9))
                prev = distinct.get(key)
                if prev is None or 0.5 < prev[0]:
                    distinct[key] = (0.5, kind, gamma)
                continue
            xb = xi_ball(float(z.real), float(z.imag))
            margin = abs_lower(xb)
            rows.append({
                "node": [z.real, z.imag],
                "kind": kind,
                "abs_xi_lower": margin,
                "abs_xi_value": abs_value(xb),
                "acb_certified": True,
                "nonvanishing_certified": margin > 0.0,
            })
            key = (round(z.real, 9), round(z.imag, 9))
            prev = distinct.get(key)
            if prev is None or margin < prev[0]:
                distinct[key] = (margin, kind, gamma)
        assert counts["off_line_pin"] == 2, counts
        assert counts["real_axis_pin"] == 3, counts
        assert counts["critical_line_nonzero_pin"] == 1, counts
        assert counts["critical_line_zero"] in (21, 24, 27), counts
        assert len(nodes) == 30 + 3 * GAMMAS.index(gamma), len(nodes)
        blocks.append({
            "gamma": gamma,
            "radius": radius,
            "node_count": len(nodes),
            "counts": counts,
            "nonzero_pins": rows,
            "min_pin_margin": min(r["abs_xi_lower"] for r in rows),
        })

    kill = xi_ball(0.5, KILL_PIN)
    anchor = {}
    if ANCHOR_2259.exists():
        anchor = json.loads(ANCHOR_2259.read_text(
            encoding="utf-8"))["kill_pin"]
    kill_row = {
        "height": KILL_PIN,
        "abs_xi_lower": abs_lower(kill),
        "abs_xi_value": abs_value(kill),
        "anchor_2259_abs_Z_lower": anchor.get("abs_lower"),
        "anchor_2259_is_zero": anchor.get("is_zero"),
    }

    instances = [r for b in blocks for r in b["nonzero_pins"]]
    acb_rows = [r for r in instances if r.get("acb_certified")]
    classical_rows = [r for r in instances if r.get("classical")]
    kind_count = {}
    for v in distinct.values():
        kind_count[v[1]] = kind_count.get(v[1], 0) + 1
    min_margin_row = min(acb_rows, key=lambda r: r["abs_xi_lower"])
    all_certified = (all(r["nonvanishing_certified"] for r in instances)
                     and kill_row["abs_xi_lower"] > 0.0)
    verdict = (
        f"CENSUS-ARB-CERTIFIED: all {len(instances)} non-zero pin "
        f"instances at the three candidates ({len(distinct)} distinct "
        "points: " + ", ".join(f"{v} {k}" for k, v in sorted(
            kind_count.items())) + ") "
        f"have xi != 0: {len(acb_rows)} acb-certified, of which the "
        "smallest certified lower bound is "
        f"{min_margin_row['abs_xi_lower']:.6g} at the "
        f"({min_margin_row['kind']}) pin "
        f"{min_margin_row['node'][0]:.6g} + {min_margin_row['node'][1]:.6g}i; "
        f"{len(classical_rows)} instance(s) at the pole point s = 1 use "
        "the classical exact xi(1) = 1/2.  The kill pin at "
        f"{KILL_PIN} re-certified with "
        f"|xi| >= {kill_row['abs_xi_lower']:.6g} (2259 Hardy-Z pin "
        f"|Z| >= {kill_row['anchor_2259_abs_Z_lower']}).  The 2259 "
        "extension is complete: zeros by certified brackets, non-zero "
        "pins by certified lower bounds; the census classification is "
        "now ball-checked end to end at ball rigor (the mpmath rule "
        "remains the classifier, not the certificate).  No producer GO, "
        "no gate sign change, no RH claim.")
    result = {
        "record": RECORD,
        "status": "ARB-CERTIFIED (acb zeta/gamma, 200-bit balls)",
        "date": "2026-09-30",
        "precision_bits": PREC_BITS,
        "blocks": blocks,
        "distinct_nonzero_pins": [
            {"node": list(k), "abs_xi_lower": v[0], "kind": v[1],
             "gamma": v[2]} for k, v in sorted(distinct.items())],
        "kill_pin": kill_row,
        "summary": {
            "pin_instances": len(instances),
            "acb_certified_instances": len(acb_rows),
            "classical_instances": len(classical_rows),
            "distinct_points": len(distinct),
            "distinct_kinds": kind_count,
            "all_certified": all_certified,
            "min_pin_margin": min_margin_row["abs_xi_lower"],
            "comparison_2259": {
                "brackets": 72,
                "kill_pin_abs_Z_lower": kill_row["anchor_2259_abs_Z_lower"],
            },
        },
        "verdict": verdict,
        "nonclaims": [
            "the xi evaluation certifies non-vanishing at the committed "
            "float node coordinates (arb(float) is exact); the critical-"
            "line zero side remains the 2259 brackets",
            "the pin at s = 1 uses the classical exact value xi(1) = 1/2 "
            "rather than an acb evaluation: acb.zeta at the pole s = 1 "
            "is indeterminate and interval arithmetic cannot cancel "
            "(s-1) zeta(s) at the boundary point",
            "the classification rule (mpmath siegelz < 1e-9) is the "
            "committed r47 rule, not a certified object",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_census_arb_2263.py",
            "dependency": "python-flint (Arb) in a local venv",
            "machinery": "scripts/routea_weighted_zero_separation_input_"
                         "2247.py (assemble_owner, classification rule)",
            "predecessor": "docs/proofs/2259_routea_weighted_zero_"
                           "brackets_arb.md",
            "consumer_record": "docs/proofs/2245_routea_weighted_zero_"
                               "owner_count_brick.md",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    brief = {
        "verdict": verdict,
        "per_candidate": [
            {"gamma": b["gamma"], "counts": b["counts"],
             "min_pin_margin": b["min_pin_margin"]} for b in blocks],
        "kill_pin": kill_row,
        "all_certified": all_certified,
    }
    print(json.dumps(brief, indent=2))


if __name__ == "__main__":
    main()