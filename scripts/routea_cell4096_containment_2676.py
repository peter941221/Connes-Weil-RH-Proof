"""Screen the exact-rational containment chain for cell 4096 against 2675.

Record 2676 prep. This script does NOT prove anything; it verifies, in exact
rational arithmetic mirrored from ConnesWeilRH.Dev.C1RouteAIntervalAlgebra,
that the per-family interval boxes built from the actual-owner geometry
(exact storedWidth^2 radii, capturedModulations2584, repaired midpoint
coefficients) land strictly inside the four exported 2675 rectangles, with
margin measured in binary64 ulps of the exported endpoints.

The Lean pins used here:
  exp(-1/2) via Real.exp_bound at n = 30 (two-sided),
  exp(-30)  = (exp(-1/2))^60 (upper pin) and (exp(-1/2))^60 lower pin,
  exp(-30/qL) = exp(-30) * exp(30 - 30/qL) with exp(t) >= 1 + t,
  cos/sin at the angle endpoint via the complex exp_bound Taylor partial
  sums at n = 2K+2, K = 12.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import re
import struct
import sys
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
CELL_ARTIFACT = ROOT / "results/2675_repaired_owner_cell_price_certificate.json"
OUTPUT = ROOT / "results/2676_cell4096_containment_screen.json"

EXP_ORDER = 30          # Real.exp_bound order for exp(-1/2)
TRIG_K = 12             # cos/sin Taylor index: error |a|^(2K+2)*(2K+3)/((2K+2)!*(2K+2))

FAC = [Fraction(math.factorial(n)) for n in range(64)]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bits_of(value: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def fraction_of_bits(bits: int) -> Fraction:
    return Fraction.from_float(struct.unpack(">d", struct.pack(">Q", bits))[0])


def ulp_of(x: Fraction) -> Fraction:
    """binary64 ulp of a finite nonzero Fraction value."""
    v = float(x)
    if v == 0.0:
        raise ValueError("ulp at zero is undefined for margin reporting")
    return Fraction.from_float(math.ulp(abs(v)))


# ---------------------------------------------------------------- interval ops
def RIadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def RIsub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def RImul(a, b):
    prods = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(prods), max(prods))


def RIpoint(x):
    return (x, x)


def RIinv_positive(a):
    if a[0] <= 0:
        raise ValueError("invPositive needs 0 < lo")
    return (Fraction(1) / a[1], Fraction(1) / a[0])


def CRmul(a, b):
    ar, ai = (a[0], a[1]), (a[2], a[3])
    br, bi = (b[0], b[1]), (b[2], b[3])
    rr = RIsub(RImul(ar, br), RImul(ai, bi))
    ii = RIadd(RImul(ar, bi), RImul(ai, br))
    return (rr[0], rr[1], ii[0], ii[1])


def CRpoint(z):
    return (z[0], z[0], z[1], z[1])


# ------------------------------------------------------------------ Lean parse
def parse_fin30_rationals(path: Path, name: str) -> list[Fraction]:
    text = path.read_text(encoding="utf-8")
    start = text.find(f"def {name} ")
    if start < 0:
        raise ValueError(f"cannot locate {name} in {path}")
    end = text.find("\ndef ", start + 1)
    end_nc = text.find("\nnoncomputable def ", start + 1)
    for stop in (end, end_nc):
        if stop >= 0:
            end = stop if end < 0 else min(end, stop)
    section = text[start:end if end > start else len(text)]
    match = re.search(r"!\[(.*)\]", section, re.S)
    if match is None:
        raise ValueError(f"cannot locate the ![] literal of {name} in {path}")
    body = match.group(1)

    def parse_scalar(token: str) -> Fraction:
        cleaned = token.strip()
        cleaned = (cleaned.replace(" ", "").replace(":ℝ", "")
                   .replace("(", "").replace(")", ""))
        if "/" in cleaned:
            left, right = cleaned.split("/", 1)
            return Fraction(int(left), int(right))
        if "." in cleaned:
            return Fraction(cleaned)
        return Fraction(int(cleaned))

    entries = []
    for token in body.split(","):
        cleaned = token.strip()
        if not cleaned:
            continue
        entries.append(parse_scalar(cleaned))
    if len(entries) != 30:
        raise ValueError(f"{name}: expected 30 entries, parsed {len(entries)}")
    return entries


# ------------------------------------------------------------------- exp pins
def exp_pins():
    half = Fraction(1, 2)
    partial = Fraction(0)
    for m in range(EXP_ORDER):
        term = (-1) ** m * half ** m / FAC[m]
        partial += term
    n = EXP_ORDER
    err = half ** n * Fraction(n + 1) / (FAC[n] * n)
    lower_base = partial - err
    upper_base = partial + err
    if lower_base <= 0:
        raise AssertionError("exp(-1/2) lower pin is not positive")
    phi_lo_base = lower_base ** 60
    phi_hi_pin = upper_base ** 60
    return partial, err, phi_lo_base, phi_hi_pin


def exp_addend_pin(t: Fraction) -> Fraction:
    """A rational LOWER pin for exp(t), t <= 0, |t| <= 1.

    Real.exp_bound at n = 5: |exp t - sum_{m<5} t^m/m!| <= |t|^5 * 6/(5!*5).
    The pin slack must stay far below one ulp of the exported endpoints: the
    repaired coefficients reach ~1e17 and the phi mass sum |c_j| phi_j is
    ~1.7e4, so a relative pin slack of s costs s * 1.7e4 absolute. The n = 3
    pin (slack |t|^3 * 2/9 ~ 3.5e-16 relative) already escapes by ~26 ulps;
    n = 5 (slack ~1e-27 relative) is 10 orders below one ulp."""
    if t > 0 or abs(t) > 1:
        raise AssertionError("exp addend pin expects -1 <= t <= 0")
    partial = 1 + t + t * t / 2 + t ** 3 / 6 + t ** 4 / 24
    err = abs(t) ** 5 * Fraction(6, 600)
    return partial - err


def trig_pins(angle: Fraction):
    partial_cos = Fraction(0)
    partial_sin = Fraction(0)
    for k in range(TRIG_K + 1):
        partial_cos += (-1) ** k * angle ** (2 * k) / FAC[2 * k]
        partial_sin += (-1) ** k * angle ** (2 * k + 1) / FAC[2 * k + 1]
    n = 2 * TRIG_K + 2
    err = abs(angle) ** n * Fraction(n + 1) / (FAC[n] * n)
    return (partial_cos - err, partial_cos + err,
            partial_sin - err, partial_sin + err)


# ------------------------------------------------------------------ main chain
def build_chain(families, base, correction, cell_right, theta_lean,
                width_lean, pins):
    """Exact-rational per-family boxes at the actual-owner geometry."""
    phi_lo_base, phi_hi_pin = pins
    zero = Fraction(0)
    x_box = (zero, cell_right)

    per_family = []
    for j in range(30):
        width = width_lean[j]
        radius = width * width
        theta = theta_lean[j]
        radius_box = (radius, radius)

        q_box = (1 - (max(abs(x_box[0]), abs(x_box[1])) / radius_box[0]) ** 2,
                 1 - (Fraction(0) / radius_box[1]) ** 2)
        if q_box[0] <= 0:
            raise AssertionError(f"family {j}: qL <= 0 (support crossing)")
        q_l = q_box[0]
        t_add = Fraction(30) - Fraction(30) / q_l
        if t_add >= 0:
            raise AssertionError(f"family {j}: expected negative exp addend")
        phi_lo_pin = phi_lo_base * exp_addend_pin(t_add)

        u_box = RImul(x_box, RIpoint(Fraction(1) / radius))
        q2_box = RImul(q_box, q_box)
        inv_q2 = RIinv_positive(q2_box)

        cos_lo, cos_hi, sin_lo, sin_hi = None, None, None, None
        if theta == 0:
            cos_box = (Fraction(1), Fraction(1))
            sin_box = (Fraction(0), Fraction(0))
            dlt = Fraction(1, 2 ** 200)
        else:
            angle_hi = theta * cell_right
            if abs(angle_hi) > 1:
                raise AssertionError(
                    f"family {j}: trig pin needs |angle| <= 1")
            pc_lo, pc_hi, ps_lo, ps_hi = trig_pins(angle_hi)
            abs_angle_sq = (abs(theta) * cell_right) ** 2
            dlt = abs_angle_sq * (1 + Fraction(1, 2 ** 100)) / 8 \
                + Fraction(1, 2 ** 200)
            chord = (angle_hi - 0) ** 2 / 8
            if chord > dlt:
                raise AssertionError(f"family {j}: chord radius exceeds dlt")
            cos_box = (min(Fraction(1), pc_lo) - dlt,
                       max(Fraction(1), pc_hi) + dlt)
            sin_box = (min(zero, ps_lo) - dlt,
                       max(zero, ps_hi) + dlt)
            cos_lo, cos_hi, sin_lo, sin_hi = pc_lo, pc_hi, ps_lo, ps_hi

        phi_box = (phi_lo_pin, phi_hi_pin)

        l1_box = RImul(RIpoint(Fraction(-60) / radius),
                       RImul(u_box, inv_q2))
        inv_q3 = RIinv_positive(RImul(q2_box, q_box))
        u2_box = RImul(u_box, u_box)
        term2 = RImul(u2_box, inv_q3)
        l2_box = RImul(RIpoint(Fraction(-60) / (radius * radius)),
                       RIadd(inv_q2, RImul(RIpoint(Fraction(4)), term2)))
        factor_re = RIadd(RIadd(l2_box, RImul(l1_box, l1_box)),
                          RIpoint(-theta * theta))
        factor_im = RImul(RIpoint(2 * theta), l1_box)

        trig_rect = (cos_box[0], cos_box[1], sin_box[0], sin_box[1])
        factor_rect = (factor_re[0], factor_re[1], factor_im[0], factor_im[1])

        per_family.append({
            "radius": radius,
            "q_l": q_l,
            "t_add": t_add,
            "phi_box": phi_box,
            "cos_box": cos_box,
            "sin_box": sin_box,
            "trig_rect": trig_rect,
            "l1_box": l1_box,
            "l2_box": l2_box,
            "factor_rect": factor_rect,
            "angle_pins": (cos_lo, cos_hi, sin_lo, sin_hi),
            "dlt": dlt,
        })
    return per_family


def channel_rects(per_family, coefficients):
    k0 = []
    k2 = []
    for j, fam in enumerate(per_family):
        c = coefficients[j]
        c_point = CRpoint((Fraction(c.real), Fraction(c.imag)))
        mid = (RImul(fam["phi_box"], fam["cos_box"])[0],
               RImul(fam["phi_box"], fam["cos_box"])[1],
               RImul(fam["phi_box"], fam["sin_box"])[0],
               RImul(fam["phi_box"], fam["sin_box"])[1])
        k0.append(CRmul(c_point, mid))
        # familySecondValue2346 = (c * phi * e^{i theta x}) * factor: the
        # phi weight rides in mid, exactly as in the k = 0 channel.
        k2.append(CRmul(CRmul(c_point, mid), fam["factor_rect"]))
    return k0, k2


def exact_midpoint_coefficients(rows, field):
    """Unrounded rational centers, used only to guard owner normalization."""
    values = []
    for row in rows:
        coefficient = row[field]
        values.append(SimpleNamespace(
            real=(Fraction(coefficient["real"]["lower_exact"])
                  + Fraction(coefficient["real"]["upper_exact"])) / 2,
            imag=(Fraction(coefficient["imag"]["lower_exact"])
                  + Fraction(coefficient["imag"]["upper_exact"])) / 2,
        ))
    return values


def aggregate(rects):
    lo_r = sum(r[0] for r in rects)
    hi_r = sum(r[1] for r in rects)
    lo_i = sum(r[2] for r in rects)
    hi_i = sum(r[3] for r in rects)
    return (lo_r, hi_r, lo_i, hi_i)


def containment(agg, exported):
    """Signed ulp margins (positive = inside) plus the inside verdict."""
    margins = {
        "re_lo_ulps": float((agg[0] - exported[0]) / ulp_of(exported[0])),
        "re_hi_ulps": float((exported[1] - agg[1]) / ulp_of(exported[1])),
        "im_lo_ulps": float((agg[2] - exported[2]) / ulp_of(exported[2])),
        "im_hi_ulps": float((exported[3] - agg[3]) / ulp_of(exported[3])),
    }
    inside = all(v > 0 for v in margins.values())
    return inside, margins


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()

    probe = load_module(
        "price2676", ROOT / "scripts/routea_repaired_owner_continuous_box_price_2670.py")
    strip = load_module(
        "strip2676", ROOT / "scripts/routea_corrected_strip_envelope_2303.py")

    repair = json.loads(probe.REPAIR.read_text(encoding="utf-8"))
    reread = json.loads(probe.REPAIR_REREAD.read_text(encoding="utf-8"))
    capture = json.loads(probe.CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    base, correction = probe.coefficient_arrays(repair["coefficient_rows"])
    coefficient_hashes = {
        "base": probe.md5_complex(base),
        "correction": probe.md5_complex(correction),
    }
    expected = {
        "base": reread["treatment"]["base_md5"],
        "correction": reread["treatment"]["corr_md5"],
    }
    if coefficient_hashes != expected:
        raise AssertionError("coefficients do not match the repaired owner")

    families, _b, _c, anchors = strip.load_owner()

    cell_artifact = json.loads(CELL_ARTIFACT.read_text(encoding="utf-8"))
    owner_md5 = cell_artifact["owner_coefficients_md5"]
    if owner_md5 != coefficient_hashes:
        raise AssertionError("2675 artifact coefficients drifted from the repair")
    cell = cell_artifact["cell"]
    if cell_artifact["cell_index"] != 4096 \
            or cell_artifact["partition_cells"] != 8192:
        raise AssertionError("expected cell 4096 of 8192")
    x_lo_bits = int(cell["cell_endpoints"]["x_lo"]["bits"], 16)
    x_hi_bits = int(cell["cell_endpoints"]["x_hi"]["bits"], 16)
    cell_right = fraction_of_bits(x_hi_bits)
    exported = {}
    for row in cell["channels"]:
        ep = row["rectangle_endpoints"]
        exported[row["name"]] = (
            fraction_of_bits(int(ep["re_lo"]["bits"], 16)),
            fraction_of_bits(int(ep["re_hi"]["bits"], 16)),
            fraction_of_bits(int(ep["im_lo"]["bits"], 16)),
            fraction_of_bits(int(ep["im_hi"]["bits"], 16)),
        )

    width_lean = parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth")
    theta_lean = parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean",
        "capturedModulations2584")

    width_match = all(
        struct.pack(">d", float(width_lean[j]))
        == struct.pack(">d", families[j][0]) for j in range(30))

    def theta_same(j):
        lean = float(theta_lean[j])
        captured = families[j][1]
        if struct.pack(">d", lean) == struct.pack(">d", captured):
            return True
        # the capture stores -0.0 for families 5/6/7; the Lean literal is
        # (0 : ℝ). Sign of an exact zero cannot move any interval endpoint.
        return lean == 0.0 and captured == 0.0

    theta_match = all(theta_same(j) for j in range(30))
    theta_signed_zero = [
        j for j in range(30)
        if struct.pack(">d", float(theta_lean[j]))
        != struct.pack(">d", families[j][1])]
    if not width_match:
        raise AssertionError("storedWidth floats do not match the owner capture")
    if not theta_match:
        raise AssertionError("capturedModulations2584 do not match the capture")

    _, _, phi_lo_base, phi_hi_pin = exp_pins()
    pins = (phi_lo_base, phi_hi_pin)
    per_family = build_chain(
        families, base, correction, cell_right, theta_lean, width_lean, pins)
    k0_base, k2_base = channel_rects(per_family, base)
    k0_corr, k2_corr = channel_rects(per_family, correction)

    exact_base = exact_midpoint_coefficients(
        repair["coefficient_rows"], "ideal_base_coefficient")
    exact_correction = exact_midpoint_coefficients(
        repair["coefficient_rows"], "ideal_correction_coefficient")
    exact_per_family = build_chain(
        families, exact_base, exact_correction, cell_right,
        theta_lean, width_lean, pins)
    exact_channels = {
        "base_M0": channel_rects(exact_per_family, exact_base)[0],
        "base_D2": channel_rects(exact_per_family, exact_base)[1],
        "correction_M0": channel_rects(exact_per_family, exact_correction)[0],
        "correction_D2": channel_rects(exact_per_family, exact_correction)[1],
    }

    report = {
        "record": 2676,
        "status": "CELL4096_CONTAINMENT_SCREEN",
        "cell_right_bits": f"0x{x_hi_bits:016x}",
        "exp_pin_order": EXP_ORDER,
        "trig_k": TRIG_K,
        "provenance": {
            "owner_coefficients_md5": coefficient_hashes,
            "captured_coefficients_md5": {
                "base": capture["base_md5"], "correction": capture["corr_md5"]},
            "width_bitwise_match": width_match,
            "theta_bitwise_match": theta_match,
            "theta_signed_zero_families": theta_signed_zero,
            "families_bitwise_anchors": {
                k: anchors[k] for k in ("families_bitwise", "base_bitwise",
                                        "corr_bitwise")},
        },
        "owner_coefficient_convention":
            "exact rational midpoint cast to binary64; subsequent interval arithmetic is exact",
        "unrounded_midpoint_diagnostic": {
            "status": "DIAGNOSTIC_ONLY_NOT_THE_REPAIRED_OWNER",
            "reason": "2670 and 2675 price the binary64 midpoint-cast coefficients",
            "channels": {},
        },
        "channels": {},
    }
    channel_rectangles = {
        "base_M0": k0_base,
        "base_D2": k2_base,
        "correction_M0": k0_corr,
        "correction_D2": k2_corr,
    }
    for name, rects in channel_rectangles.items():
        agg = aggregate(rects)
        inside, margins = containment(agg, exported[name])
        report["channels"][name] = {
            "aggregate_float": [float(v) for v in agg],
            "aggregate_exact": [str(v) for v in agg],
            "exported_float": [float(v) for v in exported[name]],
            "exported_exact": [str(v) for v in exported[name]],
            "inside_exported": inside,
            "margin_ulps": margins,
        }
        if not inside:
            print(f"FAIL {name}: aggregate escapes the exported rectangle")
            print("  signed ulp margins", margins)
            raise SystemExit(1)

        exact_agg = aggregate(exact_channels[name])
        exact_inside, exact_margins = containment(exact_agg, exported[name])
        report["unrounded_midpoint_diagnostic"]["channels"][name] = {
            "inside_exported": exact_inside,
            "margin_ulps": exact_margins,
        }

    report["status"] = "CELL4096_CONTAINMENT_SCREEN_PASS"
    args.output.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "cell_right": str(cell_right),
        "channels": {k: v["margin_ulps"] for k, v in report["channels"].items()},
    }, indent=2))


if __name__ == "__main__":
    main()
