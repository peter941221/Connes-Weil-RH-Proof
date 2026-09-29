#!/usr/bin/env python3
"""2259 - Rigorous interval re-certification of the Hardy-Z brackets via Arb
ball arithmetic (python-flint).

Consumer: the mpmath 60-dps numeric certificates of the 2251/2254
separation input.  The bracket sign changes are re-derived with certified
enclosures: Z(t) = e^{i theta(t)} zeta(1/2 + i t) is evaluated with
`acb.zeta` and `acb.lgamma` (Arb's certified complex functions) at 200-bit
precision, a sign is accepted only when the real part's ball excludes zero,
and the bisection is driven by certified signs in arb arithmetic (no float
step).  Endpoints are stored as 30-digit decimal strings plus certified
float bounds.  The nonzero kill pin is certified by a positive lower bound
of |Z|.

Writes results/2259_hardyz_arb_certification.json.

Requires python-flint (`pip install python-flint` in a venv; the system
python may be PEP-668 externally managed).
"""

import json
import math
import sys
from pathlib import Path

from flint import acb, arb, ctx  # pyright: ignore[reportMissingImports]

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_separation_input_2247 as r47  # noqa: E402

RECORD = 2259
GAMMAS = (39.25244858548658, 42.12289614653125, 45.66611208104108)
DELTA = 0.445
PREC_BITS = 200
BRACKET_HALF = 0.01
BISECT_STEPS = 80                      # 0.02 / 2^80 ~ 1.65e-26
START_MARGIN = 1e-6
KILL_PIN = 27.67032193035704
OUTPUT = ROOT / "results" / "2259_hardyz_arb_certification.json"

ctx.prec = PREC_BITS


def z_ball(t_point):
    """Certified enclosure of the Hardy-Z function at a real point."""
    t = t_point if isinstance(t_point, arb) else arb(repr(t_point))
    zeta = acb(arb("0.5"), t).zeta()
    lg = acb(arb("0.25"), t / 2).lgamma()
    theta = lg.imag - (t / 2) * arb.pi().log()
    return zeta * acb(theta.cos(), theta.sin())


def certified_sign(z_ball_value):
    """+1 / -1 when the real part's ball excludes zero, else 0."""
    mid = float(z_ball_value.real.mid())
    rad = float(z_ball_value.real.rad())
    margin = abs(mid) - rad - 8.0 * math.ulp(abs(mid) if mid else 1.0)
    if margin <= 0.0:
        return 0
    return 1 if mid > 0.0 else -1


def certified_abs_lower(z_ball_value):
    """Certified lower bound of |Re Z| (0.0 when not certified positive)."""
    mid = float(z_ball_value.real.mid())
    rad = float(z_ball_value.real.rad())
    value = abs(mid) - rad - 8.0 * math.ulp(abs(mid) if mid else 1.0)
    return value if value > 0.0 else 0.0


def ball_upper(x):
    """Certified float upper bound of a nonnegative arb ball."""
    return float(x.mid()) + float(x.rad())


def ball_lower(x):
    """Certified float lower bound of an arb ball (may be negative)."""
    return float(x.mid()) - float(x.rad())


def rigorous_bisect(height):
    a = arb(repr(height)) - BRACKET_HALF
    b = arb(repr(height)) + BRACKET_HALF
    za = z_ball(a)
    zb = z_ball(b)
    sa = certified_sign(za)
    sb = certified_sign(zb)
    if sa == 0 or sb == 0 or sa == sb:
        raise RuntimeError(f"no certified start bracket at {height}")
    if certified_abs_lower(za) < START_MARGIN \
            or certified_abs_lower(zb) < START_MARGIN:
        raise RuntimeError(f"weak start margin at {height}")
    for _ in range(BISECT_STEPS):
        m = (a + b) / 2
        zm = z_ball(m)
        sm = certified_sign(zm)
        if sm == 0:
            raise RuntimeError(f"undecided midpoint at {m}")
        if sm == sa:
            a, za, sa = m, zm, sm
        else:
            b, zb, sb = m, zm, sm
    return a, b, za, zb


def candidate_block(gamma):
    assembled = r47.assemble_owner(gamma)
    radius, nodes, values = assembled[1], assembled[2], assembled[3]
    rows = []
    nonzeros = []
    for z, v in zip(nodes, values):
        if v != 0 or abs(z.imag) <= 1e-9 or abs(z.real - 0.5) > 1e-9:
            continue
        zb = z_ball(z.imag)
        margin = certified_abs_lower(zb)
        if margin < 1e-9:
            a, b, za, zb2 = rigorous_bisect(z.imag)
            rows.append({
                "height": z.imag,
                "lo_str": a.str(30), "hi_str": b.str(30),
                "lo_float": float(a.mid()), "hi_float": float(b.mid()),
                "width_upper": ball_upper(b - a),
                "sign_lo": certified_sign(za), "sign_hi": certified_sign(zb2),
                "abs_lower_lo": certified_abs_lower(za),
                "abs_lower_hi": certified_abs_lower(zb2),
                "imag_abs_upper_lo": float(za.imag.abs_upper()),
                "imag_abs_upper_hi": float(zb2.imag.abs_upper()),
                "_a": a, "_b": b,
            })
        else:
            nonzeros.append({"height": z.imag, "abs_lower": margin})
    rows.sort(key=lambda r: float(r["_a"].mid()))
    gaps = [ball_lower(rows[i + 1]["_a"] - rows[i]["_b"])
            for i in range(len(rows) - 1)]
    endpoint_margin = min(
        min(r["abs_lower_lo"], r["abs_lower_hi"]) for r in rows)
    out_rows = [{k: v for k, v in r.items() if not k.startswith("_")}
                for r in rows]
    return {
        "gamma": gamma,
        "radius": radius,
        "critical_line_zeros": len(out_rows),
        "nonzero_pins": len(nonzeros),
        "brackets": out_rows,
        "min_pairwise_gap_lower": min(gaps) if gaps else None,
        "max_width_upper": max(r["width_upper"] for r in out_rows),
        "min_endpoint_margin_certified": endpoint_margin,
        "nonzero_pin_rows": nonzeros,
    }


def main():
    blocks = [candidate_block(gamma) for gamma in GAMMAS]
    kill = z_ball(KILL_PIN)
    kill_row = {
        "height": KILL_PIN,
        "abs_lower": certified_abs_lower(kill),
        "is_zero": certified_sign(kill) == 0,
    }
    result = {
        "record": RECORD,
        "status": "RIGOROUS-BALL-CERTIFICATES (Arb acb zeta + lgamma)",
        "date": "2026-09-30",
        "precision_bits": PREC_BITS,
        "bisect_steps": BISECT_STEPS,
        "candidates": blocks,
        "kill_pin": kill_row,
        "summary": {
            "total_brackets": sum(b["critical_line_zeros"] for b in blocks),
            "max_width_upper": max(b["max_width_upper"] for b in blocks),
            "min_pairwise_gap_lower": min(
                b["min_pairwise_gap_lower"] for b in blocks),
            "min_endpoint_margin_certified": min(
                b["min_endpoint_margin_certified"] for b in blocks),
            "comparison_2254": {
                "mpmath_total_brackets": 72,
                "mpmath_max_width": 5.293955920339377e-25,
                "mpmath_min_endpoint_margin": 2.9109288740357516e-26,
                "mpmath_min_pairwise_gap": 1.3838365945092335,
            },
        },
        "method": (
            "Z(t) = exp(i theta(t)) zeta(1/2 + i t) with theta(t) = "
            "Im log Gamma(1/4 + i t/2) - (t/2) log pi, both evaluated as "
            "Arb balls (acb.zeta, acb.lgamma); a sign is certified when the "
            "real part's ball excludes zero with a float-conversion padding "
            "of 8 ulps; brackets are bisected on certified signs in arb "
            "arithmetic; a critical-line zero exists in each bracket by IVT "
            "(Z is real analytic and the certified endpoint signs are "
            "opposite).  Endpoint floats are rounded midpoints; the "
            "certified objects are the balls (radius ~1e-57) and the "
            "30-digit decimal endpoints"),
        "nonclaims": [
            "this certifies the bracket sign changes (existence of a zero "
            "in each bracket), not the completeness of the zero list and "
            "not the separation geometry (the two-ulp float guards of 2254 "
            "stand for the geometric lower bounds)",
            "the node classification uses the same mpmath 1e-9 rule as "
            "2254 (bracket existence is then certified rigorously)",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_brackets_arb_2259.py",
            "dependency": "python-flint (Arb) in a local venv; "
            "pip install python-flint",
            "machinery": "scripts/routea_weighted_zero_separation_input_2247.py",
            "predecessor": "scripts/routea_weighted_zero_separation_certified_2254.py",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    brief = {
        "status": result["status"],
        "summary": result["summary"],
        "kill_pin": kill_row,
        "per_candidate": [
            {"gamma": b["gamma"], "brackets": b["critical_line_zeros"],
             "max_width_upper": b["max_width_upper"],
             "min_endpoint_margin": b["min_endpoint_margin_certified"]}
            for b in blocks],
    }
    print(json.dumps(brief, indent=2))


if __name__ == "__main__":
    main()