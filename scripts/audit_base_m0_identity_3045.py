#!/usr/bin/env python3
"""Record 3045: exact source-level identity audit for 2535 -> baseM0.

This checks stored rational values and binary64 decodings.  It does not claim
that the external Arb cell bounds have been imported into Lean.
"""
from __future__ import annotations
import json, re, struct
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def binary64(n: str) -> Fraction:
    return Fraction.from_float(struct.unpack(">d", int(n).to_bytes(8, "big"))[0])

def rational_block(text: str, name: str, end: str):
    block = text.split(f"noncomputable def {name}")[1].split(f"noncomputable def {end}")[0]
    toks = re.findall(r"\(\((-?\d+) : ℝ\) / (\d+)\)|\((-?\d+) : ℝ\)", block)
    return [Fraction(int(a), int(b)) if a else Fraction(int(c), 1) for a, b, c in toks]

def main():
    repair = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())
    capture = json.loads((ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    coeff_src = (ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCell2678.lean").read_text(encoding="utf-8")
    coeff_src = coeff_src.split("noncomputable def record2678BaseM0FamilyRects")[0]
    pairs = re.findall(r"⟨binary64Value2674\s+(\d+),\s*binary64Value2674\s+(\d+)⟩", coeff_src)
    coeff_ok = len(pairs) == len(repair["coefficient_rows"]) == 30
    coeff_diffs = []
    coeff_outside = []
    max_abs_delta = Fraction(0)
    for i, (real_bits, imag_bits) in enumerate(pairs):
        c = repair["coefficient_rows"][i]["ideal_base_coefficient"]
        mr = (Fraction(c["real"]["lower_exact"]) + Fraction(c["real"]["upper_exact"])) / 2
        mi = (Fraction(c["imag"]["lower_exact"]) + Fraction(c["imag"]["upper_exact"])) / 2
        rr, ii = binary64(real_bits), binary64(imag_bits)
        max_abs_delta = max(max_abs_delta, abs(rr - mr), abs(ii - mi))
        if rr != mr or ii != mi:
            coeff_diffs.append(i)
        if not (Fraction(c["real"]["lower_exact"]) <= rr <= Fraction(c["real"]["upper_exact"])) or not (Fraction(c["imag"]["lower_exact"]) <= ii <= Fraction(c["imag"]["upper_exact"])):
            coeff_outside.append(i)
    mod_src = (ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean").read_text(encoding="utf-8")
    mods = rational_block(mod_src, "capturedModulations2584", "capturedNodes2584")
    capture_mods = [Fraction.from_float(float.fromhex(row[1])) for row in capture["families_hex"]]
    modulation_ok = len(mods) == len(capture_mods) == 30 and mods == capture_mods
    result = {
        "record": 3045,
        "status": "BASE_M0_SOURCE_IDENTITY_AUDIT",
        "coefficient_count": len(pairs),
        "coefficient_midpoint_exact_matches": not coeff_diffs,
        "coefficient_differing_indices": coeff_diffs,
        "coefficient_casts_inside_2338_boxes": not coeff_outside,
        "coefficient_outside_indices": coeff_outside,
        "maximum_cast_minus_midpoint_abs": str(max_abs_delta),
        "modulation_count": len(mods),
        "modulation_exact_matches_capture": modulation_ok,
        "support_convention": "2535 uses captured width squared; Lean correctedPhysical/externalPhysical uses storedWidth^2",
        "all_source_identity_checks_pass": coeff_ok and not coeff_outside and modulation_ok,
        "nonclaims": ["no Arb-to-Lean numeric import", "no four-channel producer", "no chargeRest identity", "no RH claim"],
    }
    out = ROOT / "results/3045_base_m0_identity_audit.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
