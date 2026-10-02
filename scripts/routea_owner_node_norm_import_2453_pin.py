"""2453 pin check: bind the generated Lean literals to the artifact.

Independently re-derives, straight from the 2275 capture and the 2445
certificate positions: the coefficient/modulation literals, the 11
position literals, the bump and phase rectangles (dps-90 values with the
same 2^-200 outward margin, zero box outside support), and the composed
30-family sum rectangles (exact four-corner interval arithmetic
re-implemented here, not imported from the producer).  Every literal is
compared bitwise against the parsed module text, strict containment is
re-checked, the per-position node-norm bounds N = max|re| + max|im| are
recomposed fresh and bound against the artifact records (the Lean module
itself carries no N literals: the bridge theorem
`norm_le_of_rect_mem_2453` is the generic consumer and the Lean-side
corner evaluation is the open seam), the module sha is bound to the
artifact, and three real mutation controls (shifted phase box, perturbed
norm-bound record through the same detector, truncated module) are
fired.  Verdict PINNED-OWNER-NODE-NORM-IMPORT-VERIFIED requires every
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
CERT = ROOT / "results/2445_routea_family_endpoint_certificate.json"
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453.lean"
ARTIFACT = ROOT / "results/2453_owner_node_norm_import.json"
PIN_OUT = ROOT / "results/2453_owner_node_norm_import_pin.json"

DELTA = Fraction(1, 2 ** 200)
DPS = 90
FAMILIES = 30
POSITIONS_N = 11
EXTRA_POSITIONS = (Fraction(-1, 2), Fraction(1, 2))

REAL_RE = r"\(\((-?\d+) : ℚ\)(?: / (\d+))? : ℝ\)"
COMPLEX_RE = r"⟨" + REAL_RE + r", " + REAL_RE + r"⟩"


def pair(p):
    num, den = p
    return Fraction(num) / (Fraction(den) if den else Fraction(1))


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


def load_positions():
    cert = json.loads(CERT.read_text())
    seen = []
    for row in cert["rows"]:
        fr = Fraction.from_float(row["position"]) if row["position"] != 0.0 \
            else Fraction(0)
        if fr not in seen:
            seen.append(fr)
    seen.extend(EXTRA_POSITIONS)
    seen.sort()
    return seen


def mpf_to_fraction(v):
    sign, man, exp, _bc = mp.mpf(v)._mpf_
    if man == 0:
        return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f


def mp_fraction(fr):
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def fresh_boxes(families, pos):
    """Producer-arithmetic-order re-derivation of bump/phase boxes."""
    mp.mp.dps = DPS
    bumps, phases = [], []
    for width, modulation in families:
        radius = width * width
        if abs(pos) >= radius:
            bumps.append((Fraction(0) - DELTA, Fraction(0) + DELTA))
        else:
            quotient = 1 - (pos / radius) ** 2
            bump = mpf_to_fraction(mp.exp(
                mp_fraction(Fraction(-30) / quotient)))
            bumps.append((bump - DELTA, bump + DELTA))
        x = mp_fraction(modulation * pos)
        cos_v, sin_v = mpf_to_fraction(mp.cos(x)), mpf_to_fraction(mp.sin(x))
        phases.append(((cos_v - DELTA, cos_v + DELTA),
                       (sin_v - DELTA, sin_v + DELTA)))
    return bumps, phases


def interval_mul(a, b):
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def hull(coef_re, coef_im, bump_box, phase_boxes):
    """Composition with the producer's exact interval semantics,
    re-implemented here for the bitwise sumRect binding."""
    cri, cii = (coef_re, coef_re), (coef_im, coef_im)
    pre, pii = phase_boxes
    rr = interval_sub(interval_mul(cri, interval_mul(bump_box, pre)),
                      interval_mul(cii, interval_mul(bump_box, pii)))
    ii = interval_add(interval_mul(cri, interval_mul(bump_box, pii)),
                      interval_mul(cii, interval_mul(bump_box, pre)))
    return rr, ii


def decl_map(text):
    starts = [(m.start(), m.group(2)) for m in re.finditer(
        r'^(noncomputable def|theorem) (\S+)', text, re.M)]
    chunks = {}
    for i, (s, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        chunks[name] = text[s:end]
    return chunks


def parse_reals(chunk):
    return [real_from_match(m) for m in re.finditer(REAL_RE, chunk)]


def parse_complexes(chunk):
    vals = []
    for m in re.finditer(COMPLEX_RE, chunk):
        parts = re.findall(REAL_RE, m.group(0))
        if len(parts) == 2:
            vals.append((pair(parts[0]), pair(parts[1])))
    return vals


def n_binds(fresh, record):
    """The N-binding detector: a fresh recomposition must equal the
    artifact record's N exactly (decimal-string comparison)."""
    return record is not None and record.get("N") == str(fresh)


def main():
    failures = []
    families, base, corr = load_owner()
    positions = load_positions()
    assert len(positions) == POSITIONS_N

    lean_text = LEAN.read_text(encoding="utf-8")
    if not lean_text.endswith("end ConnesWeilRH.Dev\n"):
        failures.append("module tail guard")
    chunks = decl_map(lean_text)
    artifact = json.loads(ARTIFACT.read_text())
    artifact_boxes = artifact.get("sum_boxes_and_bounds", {})

    parsed_base = parse_complexes(chunks.get("capBaseCoef2453", ""))
    parsed_corr = parse_complexes(chunks.get("capCorrCoef2453", ""))
    parsed_mod = parse_reals(chunks.get("capMod2453", ""))
    if len(parsed_base) != FAMILIES:
        failures.append(f"base coef count {len(parsed_base)}")
    if len(parsed_corr) != FAMILIES:
        failures.append(f"corr coef count {len(parsed_corr)}")
    if len(parsed_mod) != FAMILIES:
        failures.append(f"mod count {len(parsed_mod)}")
    for k in range(FAMILIES):
        if k < len(parsed_base) and parsed_base[k] != base[k]:
            failures.append(f"base[{k}] literal != capture")
        if k < len(parsed_corr) and parsed_corr[k] != corr[k]:
            failures.append(f"corr[{k}] literal != capture")
        if k < len(parsed_mod) and parsed_mod[k] != families[k][1]:
            failures.append(f"mod[{k}] literal != capture")

    pos_mismatches = []
    rect_mismatches = []
    sum_mismatches = []
    n_mismatches = []
    containment_failures = []
    n_fresh_by = {}

    for idx in range(POSITIONS_N):
        tag = f"p{idx:02d}"
        pos = positions[idx]
        pos_parsed = parse_reals(chunks.get(f"pos2453{tag}", ""))
        if len(pos_parsed) != 1 or pos_parsed[0] != pos:
            pos_mismatches.append(f"{tag} position literal")

        bumps, phases = fresh_boxes(families, pos)
        parsed_bump = parse_reals(chunks.get(f"bumpRect2453{tag}", ""))
        parsed_phase = parse_reals(chunks.get(f"phaseRect2453{tag}", ""))
        if len(parsed_bump) != 4 * FAMILIES:
            rect_mismatches.append(f"{tag} bump count {len(parsed_bump)}")
        else:
            for k in range(FAMILIES):
                lo, hi = bumps[k]
                got = tuple(parsed_bump[4 * k:4 * k + 4])
                want = (lo, hi, Fraction(0), Fraction(0))
                if got != want:
                    rect_mismatches.append(f"{tag} bump[{k}]")
        if len(parsed_phase) != 4 * FAMILIES:
            rect_mismatches.append(f"{tag} phase count {len(parsed_phase)}")
        else:
            for k in range(FAMILIES):
                re_box, im_box = phases[k]
                got = tuple(parsed_phase[4 * k:4 * k + 4])
                want = (re_box[0], re_box[1], im_box[0], im_box[1])
                if got != want:
                    rect_mismatches.append(f"{tag} phase[{k}]")

        # independent recomposition per channel
        for channel, coefficients in (("Base", base), ("Corr", corr)):
            re_box_sum = (Fraction(0), Fraction(0))
            im_box_sum = (Fraction(0), Fraction(0))
            for k in range(FAMILIES):
                coef_re, coef_im = coefficients[k]
                rr, ii = hull(coef_re, coef_im, bumps[k], phases[k])
                re_box_sum = interval_add(re_box_sum, rr)
                im_box_sum = interval_add(im_box_sum, ii)
                radius = families[k][0] * families[k][0]
                mp.mp.dps = DPS
                if abs(pos) >= radius:
                    bump_c = Fraction(0)
                else:
                    bump_c = mpf_to_fraction(mp.exp(
                        mp_fraction(Fraction(-30) / (1 - (pos / radius) ** 2))))
                x = mp_fraction(families[k][1] * pos)
                cos_c = mpf_to_fraction(mp.cos(x))
                sin_c = mpf_to_fraction(mp.sin(x))
                re_ref = coef_re * bump_c * cos_c - coef_im * bump_c * sin_c
                im_ref = coef_re * bump_c * sin_c + coef_im * bump_c * cos_c
                if not (rr[0] <= re_ref <= rr[1] and ii[0] <= im_ref <= ii[1]):
                    containment_failures.append(f"{channel}[{k}]@{tag}")
            art_record = artifact_boxes.get(f"{channel.lower()}_{tag}")
            if art_record is None or \
                    art_record["re"] != [str(re_box_sum[0]), str(re_box_sum[1])] or \
                    art_record["im"] != [str(im_box_sum[0]), str(im_box_sum[1])]:
                sum_mismatches.append(f"{tag} {channel} sumRect")
            n_fresh = max(abs(re_box_sum[0]), abs(re_box_sum[1])) + \
                max(abs(im_box_sum[0]), abs(im_box_sum[1]))
            n_fresh_by[(channel, tag)] = n_fresh
            if not n_binds(n_fresh, art_record):
                n_mismatches.append(f"{tag} {channel} N")

    failures += pos_mismatches[:5] + rect_mismatches[:5] + \
        sum_mismatches[:5] + n_mismatches[:5] + containment_failures[:5]

    if artifact.get("lean_module_sha256") != hashlib.sha256(
            LEAN.read_bytes()).hexdigest():
        failures.append("lean module sha != artifact")

    # Mutation controls — each must FIRE through the same detectors.
    controls = []
    phases0 = fresh_boxes(families, positions[0])[1]
    shifted = [(re_box, im_box) if idx else
               ((re_box[0] + Fraction(1, 1000), re_box[1]), im_box)
               for idx, (re_box, im_box) in enumerate(phases0)]
    flat = [v for re_box, im_box in shifted
            for v in (re_box[0], re_box[1], im_box[0], im_box[1])]
    parsed_phase0 = parse_reals(chunks.get("phaseRect2453p00", ""))
    fired = len(parsed_phase0) == 4 * FAMILIES and any(
        tuple(flat[4 * k:4 * k + 4]) != tuple(parsed_phase0[4 * k:4 * k + 4])
        for k in range(FAMILIES))
    controls.append({"name": "shifted_phase_box_fires", "fired": fired})

    # Control 2: a perturbed artifact N record must be caught by the
    # same n_binds detector used for the real bindings above.
    n_fresh_p05 = n_fresh_by.get(("Base", "p05"))
    control_2_fired = n_fresh_p05 is not None and not n_binds(
        n_fresh_p05, {"N": str(n_fresh_p05 + 1)})
    controls.append({"name": "perturbed_norm_record_fires",
                     "fired": control_2_fired})

    control_3_fired = not lean_text[:-80].endswith("end ConnesWeilRH.Dev\n")
    controls.append({"name": "truncated_module_fires", "fired": control_3_fired})

    for control in controls:
        if not control["fired"]:
            failures.append("mutation control inert: " + control["name"])

    verdict = "PINNED-OWNER-NODE-NORM-IMPORT-VERIFIED" if not failures \
        else "PINNED-OWNER-NODE-NORM-IMPORT-FAILURES"
    result = {
        "record": 2453,
        "verdict": verdict,
        "failures": failures,
        "mutation_controls": controls,
        "positions": POSITIONS_N,
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
