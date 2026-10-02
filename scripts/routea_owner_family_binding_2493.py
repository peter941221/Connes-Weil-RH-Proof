"""2493: exact ownership control for the 2491 hybrid price inputs.

This compares the three parameter streams consumed by the external 2491
price with the generated Lean owner definitions in 2460/2463:
radius, modulation, and the midpoint coefficient.  It checks identity as
Fractions, not by decimal or floating-point tolerance.  This is an input
provenance control only; it does not turn the external MPFR price into a
Lean analytic enclosure certificate.
"""
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460.lean"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2493_owner_family_binding.json"


def rat(text):
    text = text.strip()
    if "/" in text:
        a, b = text.split("/", 1)
        return Fraction(int(a), int(b))
    return Fraction(int(text))


def parse_lean_defs():
    text = LEAN.read_text(encoding="utf-8")
    scalar = {}
    for name, value in re.findall(
            r"def ((?:mod|rad)\d+_2460) : ℝ := \(\(([^:]+) : ℚ\) : ℝ\)", text):
        scalar[name] = rat(value)
    complex_defs = {}
    pattern = (r"def (coef\d+_2460) : ℂ := Complex\.mk "
               r"\(\(([^:]+) : ℚ\) : ℝ\) "
               r"\(\(([^:]+) : ℚ\) : ℝ\)")
    for name, real, imag in re.findall(pattern, text):
        complex_defs[name] = (rat(real), rat(imag))
    return scalar, complex_defs


def float_fraction(hex_text):
    return Fraction.from_float(float.fromhex(hex_text))


def main():
    scalar, complex_defs = parse_lean_defs()
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    rows = repair["coefficient_rows"]
    families = capture["families_hex"]
    checks = []
    for i, (row, pair) in enumerate(zip(rows, families)):
        width = float_fraction(pair[0])
        expected = {
            "rad": width * width,
            "mod": float_fraction(pair[1]),
            "coef_re": (rat(row["ideal_base_coefficient"]["real"]["lower_exact"])
                        + rat(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2,
            "coef_im": (rat(row["ideal_base_coefficient"]["imag"]["lower_exact"])
                        + rat(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2,
        }
        actual = {
            "rad": scalar[f"rad{i}_2460"],
            "mod": scalar[f"mod{i}_2460"],
            "coef_re": complex_defs[f"coef{i}_2460"][0],
            "coef_im": complex_defs[f"coef{i}_2460"][1],
        }
        checks.append({"index": i, "equal": expected == actual,
                       "fields": {key: expected[key] == actual[key]
                                  for key in expected}})
    all_equal = all(row["equal"] for row in checks)
    result = {
        "record": 2493,
        "status": "EXACT_OWNER_INPUTS_MATCHED" if all_equal else "EXACT_OWNER_INPUT_MISMATCH",
        "scope": "2491 external price input ownership only",
        "families_checked": len(checks),
        "fields_checked": ["radius", "modulation", "coefficient_real", "coefficient_imag"],
        "all_equal": all_equal,
        "checks": checks,
        "lean_sha256": hashlib.sha256(LEAN.read_bytes()).hexdigest(),
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": ["no analytic enclosure proof", "no producer GO", "no RH"],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if not all_equal:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
