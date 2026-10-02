"""2458 (obligation W-C micro): rational-panel envelope shape probe.

The planned attachment architecture lifts the 2454 point hulls to
rational panels: over a panel [x0, x1] the bump factor is boxed by
monotonicity, the phase factors by the certified Lipschitz shape
|cos t - cos c| <= |t - c| (same for sin) around the midpoint, and the
composed 2454 hull arithmetic bounds every |F(x)| in the panel with the
complex sum composed before the modulus (A7 law).

This probe validates the shape on the 2275 capture at three panels of
the production grid spacing h = 2R/(N-1) with N = 120001: an interior
panel, a panel containing a mid-family support edge, and a panel at
the global support edge.  For each panel: containment of 5 exact
sample points, hull tightness, and per-panel timing to extrapolate the
full-grid producer cost.  Diagnostic only: no Lean module, no
certificate, no producer GO.
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp

sys.set_int_max_str_digits(200000)

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2458_panel_envelope_micro.json"

DPS_WORK = 90
DELTA = Fraction(1, 2 ** 200)
FAMILIES = 30
N_GRID = 120001
RADIUS = Fraction(65536, 10000)  # exact stand-in for the 2338 radius ~6.5536
SAMPLES = 5


def load_capture():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(Fraction(float.fromhex(width)), Fraction(float.fromhex(mod)))
                for width, mod in capture["families_hex"]]
    base = [(Fraction(float.fromhex(re)), Fraction(float.fromhex(im)))
            for re, im in capture["base_hex"]]
    return families, base


def mpf_to_fraction(v):
    sign, man, exp, _ = mp.mpf(v)._mpf_
    if man == 0:
        return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f


def exact_exp(fr):
    mp.mp.dps = DPS_WORK
    return mpf_to_fraction(mp.exp(mp.mpf(fr.numerator) / mp.mpf(fr.denominator)))


def exact_cos(fr):
    mp.mp.dps = DPS_WORK
    return mpf_to_fraction(mp.cos(mp.mpf(fr.numerator) / mp.mpf(fr.denominator)))


def exact_sin(fr):
    mp.mp.dps = DPS_WORK
    return mpf_to_fraction(mp.sin(mp.mpf(fr.numerator) / mp.mpf(fr.denominator)))


def interval_mul(a, b):
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def point_interval(x):
    return x, x


def bump_box(width, x0, x1):
    """Range of widthBump over the panel: monotone in |x| inside the
    family support, zero outside; edge-straddling boxes are clamped to
    the inside endpoint (the bump tends to 0 at the edge)."""
    radius = width * width
    xs = [x for x in (x0, x1) if abs(x) < radius]
    if not xs:
        return (Fraction(0) - DELTA, Fraction(0) + DELTA)
    hi = max(xs, key=abs)
    q_hi = 1 - (min(xs, key=abs) / radius) ** 2   # larger q -> larger bump
    q_lo = 1 - (hi / radius) ** 2
    b_hi = exact_exp(Fraction(-30) / q_hi) + DELTA
    if q_lo > 0 and len(xs) == 2:
        b_lo = exact_exp(Fraction(-30) / q_lo) - DELTA
        return (b_lo, b_hi)
    return (Fraction(0) - DELTA, b_hi)


def phase_boxes(modulation, x0, x1):
    """Certified Lipschitz boxes: with c the midpoint argument and rho
    the half-width, cos t in [cos c - rho - D, cos c + rho + D]."""
    t0, t1 = modulation * x0, modulation * x1
    c = (t0 + t1) / 2
    rho = abs(t1 - t0) / 2 + DELTA
    return (exact_cos(c) - rho, exact_cos(c) + rho), \
        (exact_sin(c) - rho, exact_sin(c) + rho)


def composed_hull(coef_re, coef_im, bump, phase):
    rr = interval_sub(interval_mul(point_interval(coef_re),
                                   interval_mul(bump, phase[0])),
                      interval_mul(point_interval(coef_im),
                                   interval_mul(bump, phase[1])))
    ii = interval_add(interval_mul(point_interval(coef_re),
                                   interval_mul(bump, phase[1])),
                      interval_mul(point_interval(coef_im),
                                   interval_mul(bump, phase[0])))
    return rr, ii


def truth_value(families, coefs, x):
    re = im = Fraction(0)
    for (width, mod), (cre, cim) in zip(families, coefs):
        radius = width * width
        if abs(x) < radius:
            q = 1 - (x / radius) ** 2
            b = exact_exp(Fraction(-30) / q)
            c, s = exact_cos(mod * x), exact_sin(mod * x)
            re += cre * b * c - cim * b * s
            im += cre * b * s + cim * b * c
    return re, im


def panel_bounds(families, coefs, x0, x1):
    rr_total = (Fraction(0), Fraction(0))
    ii_total = (Fraction(0), Fraction(0))
    for (width, mod), (cre, cim) in zip(families, coefs):
        bump = bump_box(width, x0, x1)
        phase = phase_boxes(mod, x0, x1)
        rr, ii = composed_hull(cre, cim, bump, phase)
        rr_total = interval_add(rr_total, rr)
        ii_total = interval_add(ii_total, ii)
    return rr_total, ii_total


def main():
    families, base = load_capture()
    h = 2 * RADIUS / (N_GRID - 1)
    r_mid = families[15][0] * families[15][0]
    panels = {
        "interior": (Fraction(1, 4), Fraction(1, 4) + h),
        "family_edge": (r_mid - h / 2, r_mid + h / 2),
        "global_edge": (RADIUS - 3 * h / 2, RADIUS - h / 2),
    }
    checks, panels_out = [], {}
    for name, (x0, x1) in panels.items():
        t0 = time.time()
        rr, ii = panel_bounds(families, base, x0, x1)
        elapsed = time.time() - t0
        widths, contained = [], []
        for k in range(SAMPLES):
            x = x0 + (x1 - x0) * Fraction(k, SAMPLES - 1)
            re, im = truth_value(families, base, x)
            ok = rr[0] <= re <= rr[1] and ii[0] <= im <= ii[1]
            contained.append(ok)
            checks.append(ok)
            widths.append(max(rr[1] - rr[0], ii[1] - ii[0]))
        def disp(v):
            return f"{float(v):.6e}"

        panels_out[name] = {
            "x0": str(x0), "x1": str(x1),
            "re_box_display": [disp(rr[0]), disp(rr[1])],
            "im_box_display": [disp(ii[0]), disp(ii[1])],
            "containment": contained,
            "max_width_display": disp(widths[0]),
            "seconds_per_panel": round(elapsed, 3),
        }
    # extrapolate the full-grid producer cost (2 endpoints x 2 channels)
    sec = panels_out["interior"]["seconds_per_panel"]
    full_hours = sec * N_GRID * 4 / 3600
    out = {
        "record": 2458,
        "verdict": "PANEL-ENVELOPE-SHAPE-PROBED" if all(checks)
        else "PANEL-ENVELOPE-CONTAINMENT-FAIL",
        "scope": "W-C envelope shape validation on 2275 capture panels; "
                 "diagnostic only, no Lean import, no GO, no RH claim",
        "grid_spacing_h": str(h),
        "panels": panels_out,
        "containment_all": all(checks),
        "seconds_per_panel_interior": sec,
        "full_grid_producer_hours_estimate": round(full_hours, 2),
        "producer_go": False,
        "rh_claim": False,
    }
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "verdict": out["verdict"],
        "containment_all": out["containment_all"],
        "widths": {k: v["max_width_display"] for k, v in panels_out.items()},
        "sec_per_panel": sec,
        "full_grid_hours_est": out["full_grid_producer_hours_estimate"],
    }, indent=2))


if __name__ == "__main__":
    main()
