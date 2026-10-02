"""2445: same-owner directed rectangles for the 30 family terms.

This is a finite point-box certificate. It does not claim continuum transfer,
quadrature enclosure, Lean numeric import, producer GO, or RH.
"""

import argparse
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2445_routea_family_endpoint_certificate.json"


def load_preflight():
    path = ROOT / "scripts/routea_mpfr_owner_atom_preflight_2286.py"
    spec = importlib.util.spec_from_file_location("routea_mpfr_2286", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def outward(value):
    return math.nextafter(float(value), -math.inf), math.nextafter(float(value), math.inf)


def interval_payload(value):
    return {"lo": value[0], "hi": value[1]}


def interval_sub(mpfr, left, right):
    return mpfr.binary("mpfr_sub", left, (right[1], right[0]))


def complex_mul(interval, left, right):
    real = interval_sub(interval, interval.mul(left[0], right[0]), interval.mul(left[1], right[1]))
    imag = interval.add(interval.mul(left[0], right[1]), interval.mul(left[1], right[0]))
    return real, imag


def outside_stored_support(width, position):
    return abs(Fraction.from_float(position)) >= Fraction.from_float(width) ** 2


def family_rectangle(mpfr, width, modulation, coefficient, position):
    if outside_stored_support(width, position):
        return {"real": interval_payload((0.0, 0.0)), "imag": interval_payload((0.0, 0.0)), "outside_support": True}
    radius = mpfr.mul((width, width), (width, width))
    ratio = mpfr.div(outward(position), radius)
    q = interval_sub(mpfr, outward(1.0), mpfr.mul(ratio, ratio))
    if q[0] <= 0:
        raise ValueError("interior family requires a strictly positive q interval")
    bump = mpfr.unary("mpfr_exp", mpfr.div(outward(-30.0), q))
    angle = mpfr.mul(outward(modulation), outward(position))
    phase = (mpfr.unary("mpfr_cos", angle), mpfr.unary("mpfr_sin", angle))
    coefficient_box = (outward(coefficient.real), outward(coefficient.imag))
    product = complex_mul(mpfr, coefficient_box, (bump, (0.0, 0.0)))
    real, imag = complex_mul(mpfr, product, phase)
    return {
        "real": interval_payload(real), "imag": interval_payload(imag), "outside_support": False,
        "q": interval_payload(q), "bump": interval_payload(bump),
        "phase_re": interval_payload(phase[0]), "phase_im": interval_payload(phase[1]),
    }


def run():
    mpfr = load_preflight()
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    families = [(float.fromhex(a), float.fromhex(b)) for a, b in capture["families_hex"]]
    vectors = {
        "base": [complex(float.fromhex(a), float.fromhex(b)) for a, b in capture["base_hex"]],
        "correction": [complex(float.fromhex(a), float.fromhex(b)) for a, b in capture["corr_hex"]],
    }
    if len(families) != 30 or any(len(values) != 30 for values in vectors.values()):
        raise ValueError("the current owner capture must contain 30 family rows and 30 coefficients")
    maximum_radius = max(width * width for width, _ in families)
    positions = np.linspace(-maximum_radius, maximum_radius, 9).tolist()
    rows = []
    for position in positions:
        for vector, coefficients in vectors.items():
            rows.append({
                "position": position,
                "vector": vector,
                "terms": [{"index": index, "rectangle": family_rectangle(mpfr, width, theta, coefficient, position)}
                          for index, ((width, theta), coefficient) in enumerate(zip(families, coefficients))],
            })
    files = [CAPTURE.relative_to(ROOT), Path(__file__).relative_to(ROOT),
             Path("scripts/routea_mpfr_owner_atom_preflight_2286.py")]
    return {
        "record": 2445,
        "status": "MPFR-DIRECTED-FAMILY-RECTANGLE-POINT-BOX",
        "certificate": False,
        "owner": {"families": 30, "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
                  "base_md5": capture["base_md5"], "corr_md5": capture["corr_md5"],
                  "support_half_width": maximum_radius},
        "backend": {"library": "libmpfr.so.6", "precision_bits": mpfr.PREC, "rounding": "RNDD/RNDU"},
        "validation": {"positions": positions, "position_count": len(positions), "terms_per_row": 30,
                        "vectors": list(vectors)},
        "rows": rows,
        "source_sha256": {str(path): hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in files},
        "nonclaims": ["finite point-box validation only", "no continuum or quadrature enclosure",
                       "no Lean numeric import", "no producer GO or RH claim"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    artifact = run()
    args.output.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": artifact["status"], "positions": 9, "terms": 30}))


if __name__ == "__main__":
    main()
