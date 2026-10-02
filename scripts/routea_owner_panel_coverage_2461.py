"""2461: coverage probe for the exact-radius 2460 panel envelope.

This is a diagnostic companion to 2460.  It reuses the same coefficient
balls, family parameters, interval arithmetic, and exact-mpf conversion,
but checks representative panels across both signs, zero, every family
support edge, and the global endpoints.  It is not a Lean certificate.
"""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp

from routea_owner_panel_sample_2460 import (
    FAMILIES, N_GRID, RADIUS_R, SAMPLES, exact, iadd, load_inputs,
    rect_mul, truth_value,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/2461_owner_panel_coverage.json"


def grid_panel_at(target):
    h = 2 * RADIUS_R / (N_GRID - 1)
    j = int(((target + RADIUS_R) / h).__floor__())
    j = max(0, min(N_GRID - 2, j))
    x0 = -RADIUS_R + j * h
    return x0, x0 + h, h, j


def bump_upper(f, x0, x1):
    """Exact upper endpoint for widthBump on one closed panel."""
    radius = f["radius"]
    lo = max(x0, -radius)
    hi = min(x1, radius)
    if lo >= hi:
        return Fraction(0)
    closest = Fraction(0) if lo <= 0 <= hi else (
        lo if abs(lo) <= abs(hi) else hi)
    q = 1 - (closest / radius) ** 2
    return exact(mp.exp, Fraction(-30) / q)


def panel_check(fams, x0, x1):
    sum_re = (Fraction(0), Fraction(0))
    sum_im = (Fraction(0), Fraction(0))
    family_ok = []
    for f in fams:
        bump = ((Fraction(0), bump_upper(f, x0, x1)),
                (Fraction(0), Fraction(0)))
        coeff = ((f["re_lo"], f["re_hi"]), (f["im_lo"], f["im_hi"]))
        c_mid = exact(mp.cos, f["mod"] * ((x0 + x1) / 2))
        s_mid = exact(mp.sin, f["mod"] * ((x0 + x1) / 2))
        rho = abs(f["mod"]) * (x1 - x0) / 2
        phase = ((c_mid - rho, c_mid + rho),
                 (s_mid - rho, s_mid + rho))
        box = rect_mul(rect_mul(coeff, bump), phase)
        sum_re = iadd(sum_re, box[0])
        sum_im = iadd(sum_im, box[1])
        ok = True
        for sample in range(SAMPLES):
            x = x0 + (x1 - x0) * Fraction(sample, SAMPLES - 1)
            tr, ti = truth_value(f, x)
            ok = ok and box[0][0] <= tr <= box[0][1]
            ok = ok and box[1][0] <= ti <= box[1][1]
        family_ok.append(ok)

    sum_ok = True
    for sample in range(SAMPLES):
        x = x0 + (x1 - x0) * Fraction(sample, SAMPLES - 1)
        tr = ti = Fraction(0)
        for f in fams:
            fr, fi = truth_value(f, x)
            tr += fr
            ti += fi
        sum_ok = sum_ok and sum_re[0] <= tr <= sum_re[1]
        sum_ok = sum_ok and sum_im[0] <= ti <= sum_im[1]
    return all(family_ok), sum_ok


def main():
    fams, pins = load_inputs()
    targets = [("negative-interior", Fraction(-1, 4)),
               ("zero", Fraction(0)),
               ("positive-interior", Fraction(1, 4))]
    for k, f in enumerate(fams):
        targets.append((f"family-edge-{k}", f["radius"]))
        targets.append((f"family-edge-neg-{k}", -f["radius"]))
    # Include both panels adjacent to the global endpoints.
    targets.extend([("global-left", -RADIUS_R), ("global-right", RADIUS_R)])

    rows = []
    seen = set()
    for label, target in targets:
        x0, x1, h, index = grid_panel_at(target)
        key = (x0, x1)
        if key in seen:
            continue
        seen.add(key)
        fam_ok, sum_ok = panel_check(fams, x0, x1)
        rows.append({"label": label, "index": index, "x0": str(x0),
                     "x1": str(x1), "h": str(h),
                     "family_containment": fam_ok, "sum_containment": sum_ok})

    out = {
        "record": 2461,
        "verdict": "OWNER-PANEL-COVERAGE-PASS" if all(
            r["family_containment"] and r["sum_containment"] for r in rows)
        else "OWNER-PANEL-COVERAGE-FAIL",
        "scope": "diagnostic exact-mpf panel coverage; not a Lean certificate",
        "N_grid": N_GRID,
        "radius_exact": str(RADIUS_R),
        "repair_sha256": pins["repair_sha256"],
        "capture_sha256": pins["capture_sha256"],
        "panels": rows,
        "panel_count": len(rows),
    }
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n",
                   encoding="utf-8")
    print(json.dumps({"verdict": out["verdict"], "panel_count": len(rows),
                      "failed": [r["label"] for r in rows
                                 if not (r["family_containment"] and
                                         r["sum_containment"])]},
                     indent=2))


if __name__ == "__main__":
    main()
