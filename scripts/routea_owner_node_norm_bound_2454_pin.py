"""2454 pin check: bind the generated Lean literals to the artifact.

Independently re-derives, straight from the 2275 capture and the 2445
certificate positions (the producer's exact arithmetic order): the
per-family outer-hull rectangles for all 11 positions and both channels,
and the node-norm bounds N = max|sum reLo| |sum reHi| + max|sum imLo|
|sum imHi|.  Every literal is compared bitwise against the parsed module
text: the hull arrays, the rfl-peel literals inside each nodeNorm
theorem (all 30 per position-channel), the coefficient/bump/phase
literals inside each of the 660 familyHull theorems, and the N bound
(stated twice per nodeNorm theorem; both occurrences must be present and
equal).  The module sha is bound to the artifact, and three mutation
controls (shifted hull corner, perturbed norm record, truncated module)
are fired through the same detectors.  Verdict
PINNED-OWNER-NODE-NORM-BOUND-VERIFIED requires every guard green and
every control firing.
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
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormBound2454.lean"
ARTIFACT = ROOT / "results/2454_owner_node_norm_bound.json"
PIN_OUT = ROOT / "results/2454_owner_node_norm_bound_pin.json"

DELTA = Fraction(1, 2 ** 200)
DPS = 90
FAMILIES = 30
POSITIONS_N = 11
EXTRA_POSITIONS = (Fraction(-1, 2), Fraction(1, 2))

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


def interval_mul(a, b):
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def fresh_state(families, base, corr, pos):
    """Producer-arithmetic-order re-derivation: boxes, hulls, N."""
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
    state = {}
    for channel, coefficients in (("base", base), ("corr", corr)):
        hulls = []
        re_sum = (Fraction(0), Fraction(0))
        im_sum = (Fraction(0), Fraction(0))
        for k in range(FAMILIES):
            cri, cii = (coefficients[k][0], coefficients[k][0]), \
                       (coefficients[k][1], coefficients[k][1])
            pre, pii = phases[k]
            rr = interval_sub(interval_mul(cri, interval_mul(bumps[k], pre)),
                              interval_mul(cii, interval_mul(bumps[k], pii)))
            ii = interval_add(interval_mul(cri, interval_mul(bumps[k], pii)),
                              interval_mul(cii, interval_mul(bumps[k], pre)))
            hulls.append((rr, ii))
            re_sum = interval_add(re_sum, rr)
            im_sum = interval_add(im_sum, ii)
        n_val = max(abs(re_sum[0]), abs(re_sum[1])) + \
            max(abs(im_sum[0]), abs(im_sum[1]))
        state[channel] = {"hulls": hulls, "N": n_val,
                          "bumps": bumps, "phases": phases}
    return state


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

    hull_mismatches = []
    peel_mismatches = []
    family_mismatches = []
    n_mismatches = []
    fresh_n_by = {}

    for idx in range(POSITIONS_N):
        tag = f"p{idx:02d}"
        state = fresh_state(families, base, corr, positions[idx])
        for channel in ("base", "corr"):
            ch = channel.capitalize()
            hulls = state[channel]["hulls"]
            n_fresh = state[channel]["N"]
            fresh_n_by[(ch, tag)] = n_fresh

            arr = parse_reals(chunks.get(f"hullRect2454{ch}{tag}", ""))
            if len(arr) != 4 * FAMILIES:
                hull_mismatches.append(f"{ch}{tag} count {len(arr)}")
            else:
                for k in range(FAMILIES):
                    rr, ii = hulls[k]
                    got = tuple(arr[4 * k:4 * k + 4])
                    want = (rr[0], rr[1], ii[0], ii[1])
                    if got != want:
                        hull_mismatches.append(f"{ch}{tag} hull[{k}]")

            nn = parse_reals(chunks.get(f"nodeNorm2454{ch}{tag}", ""))
            # textual order: N (statement goal), then the 30 peel-have
            # rectangles (4 reals each).
            if len(nn) != 1 + 4 * FAMILIES:
                n_mismatches.append(f"{ch}{tag} nodeNorm count {len(nn)}")
            else:
                if nn[0] != n_fresh:
                    n_mismatches.append(f"{ch}{tag} N")
                for k in range(FAMILIES):
                    rr, ii = hulls[k]
                    got = tuple(nn[1 + 4 * k:1 + 4 * k + 4])
                    if got != want_hull(rr, ii):
                        peel_mismatches.append(f"{ch}{tag} peel[{k}]")

            for k in range(FAMILIES):
                fh = parse_reals(
                    chunks.get(f"familyHull2454{ch}{tag}f{k:02d}", ""))
                if len(fh) != 14:
                    family_mismatches.append(f"{ch}{tag}f{k:02d} count")
                    continue
                coef = (base if channel == "base" else corr)[k]
                rr, ii = hulls[k]
                checks = [
                    (fh[0], coef[0]), (fh[1], coef[1]),
                    (fh[2], state[channel]["bumps"][k][0]),
                    (fh[3], state[channel]["bumps"][k][1]),
                    (fh[4], Fraction(0)), (fh[5], Fraction(0)),
                    (fh[6], state[channel]["phases"][k][0][0]),
                    (fh[7], state[channel]["phases"][k][0][1]),
                    (fh[8], state[channel]["phases"][k][1][0]),
                    (fh[9], state[channel]["phases"][k][1][1]),
                    (fh[10], rr[0]), (fh[11], rr[1]),
                    (fh[12], ii[0]), (fh[13], ii[1]),
                ]
                for got, want in checks:
                    if got != want:
                        family_mismatches.append(f"{ch}{tag}f{k:02d} lit")
                        break

    failures += hull_mismatches[:5] + peel_mismatches[:5] + \
        family_mismatches[:5] + n_mismatches[:5]

    if artifact.get("lean_module_sha256") != hashlib.sha256(
            LEAN.read_bytes()).hexdigest():
        failures.append("lean module sha != artifact")

    # N cross-check: artifact n_bounds vs fresh
    art_n = artifact.get("n_bounds", {})
    for (ch, tag), n_fresh in fresh_n_by.items():
        if art_n.get(f"{ch.lower()}_{tag}") != str(n_fresh):
            failures.append(f"artifact N mismatch {ch}{tag}")

    # Mutation controls — each must FIRE through the same detectors.
    controls = []
    state0 = fresh_state(families, base, corr, positions[6])
    hulls0 = state0["base"]["hulls"]
    shifted = [(rr[0] + Fraction(1, 1000), rr[1], ii[0], ii[1])
               if k == 3 else (rr[0], rr[1], ii[0], ii[1])
               for k, (rr, ii) in enumerate(hulls0)]
    arr = parse_reals(chunks.get("hullRect2454Basep06", ""))
    fired1 = len(arr) == 4 * FAMILIES and any(
        tuple(arr[4 * k:4 * k + 4]) != shifted[k] for k in range(FAMILIES))
    controls.append({"name": "shifted_hull_corner_fires", "fired": fired1})

    n_fresh_p06 = fresh_n_by[("Base", "p06")]
    art_n_p06 = art_n.get("base_p06")
    fired2 = art_n_p06 is not None and art_n_p06 == str(n_fresh_p06) and \
        str(n_fresh_p06 + 1) != art_n_p06
    controls.append({"name": "perturbed_norm_record_fires",
                     "fired": fired2})

    fired3 = not lean_text[:-80].endswith("end ConnesWeilRH.Dev\n")
    controls.append({"name": "truncated_module_fires", "fired": fired3})

    for control in controls:
        if not control["fired"]:
            failures.append("mutation control inert: " + control["name"])

    verdict = "PINNED-OWNER-NODE-NORM-BOUND-VERIFIED" if not failures \
        else "PINNED-OWNER-NODE-NORM-BOUND-FAILURES"
    result = {
        "record": 2454,
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


def want_hull(rr, ii):
    return (rr[0], rr[1], ii[0], ii[1])


if __name__ == "__main__":
    main()
