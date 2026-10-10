"""Price one exact panel contribution before the Lean assembly theorem."""

import json
import mpmath as mp
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def frac(s):
    return F(s)


def cadd(a, b): return (a[0] + b[0], a[1] + b[1])
def csub(a, b): return (a[0] - b[0], a[1] - b[1])
def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cscale(x, a): return (x * a[0], x * a[1])
def l1(a): return abs(a[0]) + abs(a[1])


def main():
    amp = json.loads((ROOT / "results/2657_amp_pins.json").read_text())
    phase = json.loads((ROOT / "results/2658_phase_pins.json").read_text())
    tables = json.loads((ROOT / "results/2655_panel_tables.json").read_text())
    analytic = json.loads((ROOT / "results/2656_panel_analytic.json").read_text())
    panel = 95
    a = next(row for row in amp["panels"] if row["panel"] == panel)
    p = next(row for row in phase["phases"] if row["panel"] == panel)
    t = next(row for row in tables["panels"] if row["panel"] == panel)
    an = next(row for row in analytic["panels"] if row["panel"] == panel)
    amp_center = frac(a["amp_value"])
    amp_radius = frac(a["amp_radius"])
    rot_center = (frac(p["real"]), frac(p["imag"]))
    rot_radius = frac(p["radius"])
    integral = (frac(t["integral_re"]), frac(t["integral_im"]))
    center = cscale(amp_center, cmul(rot_center, integral))
    # L1 product enclosure: |ab|_1 <= |a|_1 |b|_1.  This is deliberately
    # conservative and is the quantity the Lean error-propagation lemma must
    # reproduce before any cancellation-sensitive tightening.
    amp_scale = amp_center + amp_radius
    rot_scale = l1(rot_center) + rot_radius
    int_scale = l1(integral)
    charge = (amp_radius * rot_scale * int_scale
              + amp_scale * rot_radius * int_scale)
    residual = an.get("residual_upper")
    payload = {
        "record": 2659, "panel": panel,
        "amp_center": str(amp_center), "amp_radius": str(amp_radius),
        "rotation_center": [str(x) for x in rot_center],
        "rotation_radius": str(rot_radius),
        "integral_center": [str(x) for x in integral],
        "integral_l1": str(int_scale),
        "contribution_center": [str(x) for x in center],
        "product_rounding_charge": str(charge),
        "analytic_residual_upper": residual,
        "analytic_var": an["var"],
        "scope": "P095 assembly pricing only; no Lean containment theorem",
    }
    with mp.workdps(80):
        payload["center_float"] = [float(center[0]), float(center[1])]
        payload["charge_float"] = float(charge)
    (ROOT / "results/2659_panel095_assembly_pricing.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
