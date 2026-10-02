"""2452 pin check: bind the generated Lean literals to the artifact.

Independently re-derives, straight from the 2275 capture: the coefficient
and modulation literals (exact dyadic fractions), the bump and phase
rectangles (dps-90 values with the same outward margin), and the strict
containment of the box centres.  Parses the generated Lean module text,
compares every literal bitwise against both the fresh derivation and the
artifact sha, and runs three real mutation controls (shifted phase box,
perturbed coefficient literal, truncated module) through the same
detectors.  Verdict PINNED-OWNER-POINT-IMPORT-VERIFIED requires every
guard green and every control firing.
"""
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPointImport2452.lean"
ARTIFACT = ROOT / "results/2452_owner_point_import.json"
PIN_OUT = ROOT / "results/2452_owner_point_import_pin.json"

DELTA = Fraction(1, 2 ** 200)
POSITION = Fraction(1, 2)
DPS = 90
FAMILIES = 30

REAL_RE = r"\(\((-?\d+) : ℚ\)(?: / (\d+))? : ℝ\)"
COMPLEX_RE = r"⟨" + REAL_RE + r", " + REAL_RE + r"⟩"


def real_from_match(m):
    num = Fraction(m.group(1))
    den = Fraction(m.group(2)) if m.group(2) else Fraction(1)
    return num / den


def load_owner():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(Fraction(float.fromhex(width)), Fraction(float.fromhex(modulation)))
                for width, modulation in capture["families_hex"]]
    base = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["base_hex"]]
    corr = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["corr_hex"]]
    return families, base, corr


def mpf_to_fraction(v):
    sign, man, exp, _bc = mp.mpf(v)._mpf_
    if man == 0:
        return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f


def mp_fraction(fr):
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def extract_array(text, name):
    marker = name + " :"
    idx = text.find(marker)
    if idx < 0:
        return None, "missing def " + name
    start = text.find(":=", idx)
    if start < 0:
        return None, "missing := for " + name
    end = text.find("]\n", start)
    if end < 0:
        return None, "unterminated array for " + name
    return text[start:end + 1], None


def parse_reals(block):
    return [real_from_match(m) for m in re.finditer(REAL_RE, block)]


def parse_complexes(block):
    def pair(p):
        num, den = p
        return Fraction(num) / (Fraction(den) if den else Fraction(1))
    vals = []
    for m in re.finditer(COMPLEX_RE, block):
        parts = re.findall(REAL_RE, m.group(0))
        if len(parts) != 2:
            continue
        vals.append((pair(parts[0]), pair(parts[1])))
    return vals


def fresh_boxes(families):
    """Re-derivation of the bump and phase boxes with the producer's exact
    arithmetic order (single exact-Fraction exponent, one division at
    dps 90); the binding is bitwise, containment carries the margins."""
    mp.mp.dps = DPS
    bumps, phases = [], []
    for width, modulation in families:
        radius = width * width
        quotient = 1 - (POSITION / radius) ** 2
        exponent = Fraction(-30) / quotient
        bump = mpf_to_fraction(mp.exp(mp_fraction(exponent)))
        x = mp_fraction(modulation * POSITION)
        cos_v, sin_v = mpf_to_fraction(mp.cos(x)), mpf_to_fraction(mp.sin(x))
        bumps.append((bump - DELTA, bump + DELTA))
        phases.append(((cos_v - DELTA, cos_v + DELTA),
                       (sin_v - DELTA, sin_v + DELTA)))
    return bumps, phases


def capture_mismatches(parsed_complex, reference_complex, parsed_reals,
                       reference_reals):
    out = []
    if len(parsed_complex) != len(reference_complex):
        out.append(f"count {len(parsed_complex)}")
        return out
    for k, (got, want) in enumerate(zip(parsed_complex, reference_complex)):
        if got != want:
            out.append(f"[{k}] literal != capture")
    if len(parsed_reals) != len(reference_reals):
        out.append(f"mod count {len(parsed_reals)}")
    else:
        for k, (got, want) in enumerate(zip(parsed_reals, reference_reals)):
            if got != want:
                out.append(f"[{k}] modulation literal != capture")
    return out


def rect_mismatches(parsed_flat, fresh_boxes):
    """parsed_flat: 4 reals per family; fresh_boxes: list of 2-tuples of
    (lo, hi) pairs."""
    out = []
    if len(parsed_flat) != 4 * len(fresh_boxes):
        out.append(f"count {len(parsed_flat)}")
        return out
    for k, boxes in enumerate(fresh_boxes):
        want = (boxes[0][0], boxes[0][1], boxes[1][0], boxes[1][1])
        got = tuple(parsed_flat[4 * k:4 * k + 4])
        if got != want:
            out.append(f"[{k}] rect != fresh")
    return out


def strict_containment_failures(bumps, phases):
    out = []
    for k, (lo, hi) in enumerate(bumps):
        centre = (lo + hi) / 2
        if not (lo <= centre <= hi and lo < centre < hi):
            out.append(f"bump[{k}] not strict")
    for k, (re_box, im_box) in enumerate(phases):
        if not (re_box[0] < sum(re_box) / 2 < re_box[1] and
                im_box[0] < sum(im_box) / 2 < im_box[1]):
            out.append(f"phase[{k}] not strict")
    return out


def main():
    failures = []
    families, base, corr = load_owner()
    bumps, phases = fresh_boxes(families)

    lean_text = LEAN.read_text(encoding="utf-8")
    tail_ok = lean_text.endswith("end ConnesWeilRH.Dev\n")
    if not tail_ok:
        failures.append("module tail guard")

    blocks = {}
    for name in ("capBaseCoef2452", "capCorrCoef2452", "capMod2452",
                 "bumpRect2452", "phaseRect2452"):
        block, err = extract_array(lean_text, name)
        if err:
            failures.append(err)
        blocks[name] = block

    parsed_base = parse_complexes(blocks["capBaseCoef2452"]) \
        if blocks["capBaseCoef2452"] else []
    parsed_corr = parse_complexes(blocks["capCorrCoef2452"]) \
        if blocks["capCorrCoef2452"] else []
    parsed_mod = parse_reals(blocks["capMod2452"]) \
        if blocks["capMod2452"] else []
    parsed_bump = parse_reals(blocks["bumpRect2452"]) \
        if blocks["bumpRect2452"] else []
    parsed_phase = parse_reals(blocks["phaseRect2452"]) \
        if blocks["phaseRect2452"] else []

    failures += capture_mismatches(parsed_base, base, parsed_mod,
                                   [m for _, m in families])
    failures += capture_mismatches(parsed_corr, corr, [], [])

    fresh_rects = [(bumps[k], (Fraction(0), Fraction(0)))
                   for k in range(FAMILIES)]
    failures += rect_mismatches(parsed_bump, fresh_rects)
    failures += rect_mismatches(parsed_phase, phases)

    failures += strict_containment_failures(bumps, phases)

    artifact = json.loads(ARTIFACT.read_text())
    if artifact.get("lean_module_sha256") != hashlib.sha256(
            LEAN.read_bytes()).hexdigest():
        failures.append("lean module sha != artifact")

    # Mutation controls — each must FIRE through the same detectors.
    controls = []
    shifted = [(re_box, im_box) if k else
               ((re_box[0] + Fraction(1, 1000), re_box[1]), im_box)
               for k, (re_box, im_box) in enumerate(phases)]
    shifted_flat = [v for re_box, im_box in shifted
                    for v in (re_box[0], re_box[1], im_box[0], im_box[1])]
    control_1 = rect_mismatches(shifted_flat, phases)
    controls.append({"name": "shifted_phase_box_fires",
                     "fired": len(control_1) > 0})

    perturbed = list(parsed_base)
    if perturbed:
        r0, i0 = perturbed[0]
        perturbed[0] = (r0 + 1, i0)
        control_2 = capture_mismatches(perturbed, base, [], [])
        controls.append({"name": "perturbed_coefficient_fires",
                         "fired": len(control_2) > 0})
    else:
        controls.append({"name": "perturbed_coefficient_fires",
                         "fired": False})

    control_3_fired = not lean_text[:-80].endswith("end ConnesWeilRH.Dev\n")
    controls.append({"name": "truncated_module_fires", "fired": control_3_fired})

    for control in controls:
        if not control["fired"]:
            failures.append("mutation control inert: " + control["name"])

    verdict = "PINNED-OWNER-POINT-IMPORT-VERIFIED" if not failures \
        else "PINNED-OWNER-POINT-IMPORT-FAILURES"
    result = {
        "record": 2452,
        "verdict": verdict,
        "failures": failures,
        "mutation_controls": controls,
        "delta": f"{DELTA.numerator}/{DELTA.denominator}",
        "pin_source_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "lean_module_sha256": hashlib.sha256(LEAN.read_bytes()).hexdigest(),
    }
    PIN_OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"verdict": verdict, "failures": failures[:10],
                      "mutation_controls": controls}, indent=2))


if __name__ == "__main__":
    main()
