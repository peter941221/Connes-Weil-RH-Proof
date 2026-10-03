"""2529: directed-MPFR narrow point-node replay.

This is a node-only diagnostic for the 2528 representation.  It keeps each
2338 coefficient rectangle and the exact point bump/phase intervals narrow,
adds all 30 complex rectangles first, then takes the rectangle norm.  It is
not a Lean payload: the binary64 endpoints are exported for comparison and
source-hash auditing only.
"""
import hashlib
import importlib.util
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2529_signed_point_node_mpfr.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2286", ROOT / "scripts/routea_mpfr_owner_atom_preflight_2286.py"
)
mpfr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mpfr)


def frac(text) -> Fraction:
    if isinstance(text, Fraction):
        return text
    if isinstance(text, float):
        return Fraction.from_float(text)
    a = text.split("/")
    return Fraction(int(a[0]), int(a[1])) if len(a) == 2 else Fraction(int(a[0]))


def iv_frac(value: Fraction):
    x = float(value)
    return math.nextafter(x, -math.inf), math.nextafter(x, math.inf)


def iv_float(value: float):
    return math.nextafter(value, -math.inf), math.nextafter(value, math.inf)


def add(a, b):
    return mpfr.add(a, b)


def sub(a, b):
    lo = mpfr.sub((a[0], a[0]), (b[1], b[1]))[0]
    hi = mpfr.sub((a[1], a[1]), (b[0], b[0]))[1]
    return lo, hi


def mul(a, b):
    return mpfr.mul(a, b)


def div(a, b):
    return mpfr.div(a, b)


def add_rect(a, b):
    return add(a[0], b[0]), add(a[1], b[1])


def sub_rect(a, b):
    return sub(a, b)


def rect_mul(a, b):
    ar, ai = a
    br, bi = b
    return sub_rect(mul(ar, br), mul(ai, bi)), add(mul(ar, bi), mul(ai, br))


def rect_norm_upper(z):
    re = max(abs(z[0][0]), abs(z[0][1]))
    im = max(abs(z[1][0]), abs(z[1][1]))
    return math.nextafter(re + im, math.inf)


def main() -> None:
    cells = int(sys.argv[1]) if len(sys.argv) > 1 else 2560
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re_lo = frac(row["ideal_base_coefficient"]["real"]["lower_exact"])
        re_hi = frac(row["ideal_base_coefficient"]["real"]["upper_exact"])
        im_lo = frac(row["ideal_base_coefficient"]["imag"]["lower_exact"])
        im_hi = frac(row["ideal_base_coefficient"]["imag"]["upper_exact"])
        families.append(
            {
                "coef": (iv_frac(re_lo)[0], iv_frac(re_hi)[1]),
                "imag": (iv_frac(im_lo)[0], iv_frac(im_hi)[1]),
                "radius": frac(float.fromhex(pair[0])) ** 2,
                "mod": float.fromhex(pair[1]),
            }
        )

    radius = frac("65536001/10000000")
    step = 2 * radius / cells
    rows = {"-0.5": [], "0.5": []}
    for index in range(cells + 1):
        x = -radius + index * step
        xi = iv_frac(x)
        total = ((0.0, 0.0), (0.0, 0.0))
        for family in families:
            r = family["radius"]
            if abs(x) >= r:
                continue
            x_over_r = div(xi, iv_frac(r))
            qv = sub(iv_frac(Fraction(1)), mul(x_over_r, x_over_r))
            bump = mpfr.unary("mpfr_exp", div(iv_frac(Fraction(-30)), qv))
            angle = mul(iv_float(family["mod"]), xi)
            phase = (mpfr.unary("mpfr_cos", angle), mpfr.unary("mpfr_sin", angle))
            coeff = (family["coef"], family["imag"])
            total = add_rect(total, rect_mul(rect_mul(coeff, (bump, (0.0, 0.0))), phase))
        norm = rect_norm_upper(total)
        for sigma in ("-0.5", "0.5"):
            weight = mpfr.unary("mpfr_exp", mul(iv_frac(Fraction(sigma)), xi))
            weighted = mul((norm, norm), weight)[1]
            rows[sigma].append({"index": index, "x": str(x), "upper": repr(weighted)})

    composite = {}
    for sigma, values in rows.items():
        total = (0.0, 0.0)
        for i in range(cells):
            left = (0.5 * float(values[i]["upper"]),) * 2
            right = (0.5 * float(values[i + 1]["upper"]),) * 2
            total = add(total, add(left, right))
        composite[sigma] = mpfr.mul(iv_frac(step), total)[1]

    payload = {
        "record": 2529,
        "status": "MPFR_DIRECTED_SIGNED_POINT_NODE_REPLAY_NOT_LEAN_CERTIFICATE",
        "cells": cells,
        "node_count": cells + 1,
        "radius": str(radius),
        "step": str(step),
        "backend": {"library": "libmpfr.so.6", "precision_bits": mpfr.PREC, "rounding": "RNDD/RNDU"},
        "composite_node_upper": composite,
        "rows": rows,
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": ["no curvature enclosure", "no Lean import", "no producer GO", "no SourceRH", "no RH"],
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"record": 2529, "status": payload["status"], "cells": cells, "composite_node_upper": composite, "artifact": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()


