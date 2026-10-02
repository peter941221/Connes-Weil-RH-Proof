"""2454: Lean node-norm bounds N for the 2453 import positions.

Upgrades the per-position node-norm bounds from artifact grade to Lean
theorem grade.  For each of the 11 positions (nine exact binary64
positions of the 2445/2449 certificate plus the strip endpoints +-1/2)
and each channel, emits:

- a literal outer-hull array (per family, the composed four-corner hull
  of coefficient x bump-box x phase-boxes with the producer's exact
  interval semantics, same arithmetic order as 2453);
- per family, a hull-containment theorem transporting the 2453 product
  rectangle into the literal hull through `mem_of_rect_subset_2454`,
  with the four corner comparisons discharged by rfl-peels + interval
  algebra unfolding + norm_num on exact rationals;
- a right-associated chain rectangle and a sum-containment theorem
  assembling the 30 hulls under the unfolded 30-term sum
  (`Fin.sum_univ_succ` + mem_add chain, the 2452 proof shape at scale);
- the node-norm theorem `nodeNorm2454{Base,Corr}{tag}`:
  ||correctedPhysical ...|| <= N, with N the exact rational
  max|sum reLo| |sum reHi| + max|sum imLo| |sum imHi|, discharged by
  rfl-peels + `ComplexRect2427.add` unfolding + norm_num.

Cross-record gate: the composed chain corners are checked bitwise
against the 2453 artifact sum boxes (same capture, same arithmetic
order).  Scope: 11 positions, containment/norm bounds only; no strip
norm, no quadrature import, no producer GO, no RH claim.
"""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
CERT = ROOT / "results/2445_routea_family_endpoint_certificate.json"
ART_2453 = ROOT / "results/2453_owner_node_norm_import.json"
LEAN_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormBound2454.lean"
AUDIT_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerNodeNormBound2454Audit.lean"
ARTIFACT_OUT = ROOT / "results/2454_owner_node_norm_bound.json"

DPS_WORK = 90
DELTA = Fraction(1, 2 ** 200)
EXTRA_POSITIONS = (Fraction(-1, 2), Fraction(1, 2))
FAMILIES = 30


def load_owner():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(Fraction(float.fromhex(width)), Fraction(float.fromhex(modulation)))
                for width, modulation in capture["families_hex"]]
    base = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["base_hex"]]
    corr = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["corr_hex"]]
    return families, base, corr, capture


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


def exact_exp(fraction):
    mp.mp.dps = DPS_WORK
    return mpf_to_fraction(mp.exp(mp_fraction(fraction)))


def exact_cos_sin(fraction):
    mp.mp.dps = DPS_WORK
    x = mp_fraction(fraction)
    return mpf_to_fraction(mp.cos(x)), mpf_to_fraction(mp.sin(x))


def interval_mul(a, b):
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def point_interval(x):
    return x, x


def composed_hull(coef_re, coef_im, bump_box, phase_boxes):
    coef_re_i, coef_im_i = point_interval(coef_re), point_interval(coef_im)
    phase_re_i, phase_im_i = phase_boxes
    rr = interval_sub(interval_mul(coef_re_i, interval_mul(bump_box, phase_re_i)),
                      interval_mul(coef_im_i, interval_mul(bump_box, phase_im_i)))
    ii = interval_add(interval_mul(coef_re_i, interval_mul(bump_box, phase_im_i)),
                      interval_mul(coef_im_i, interval_mul(bump_box, phase_re_i)))
    return rr, ii


def reference_term(coef_re, coef_im, bump, cos_v, sin_v):
    re_val = coef_re * bump * cos_v - coef_im * bump * sin_v
    im_val = coef_re * bump * sin_v + coef_im * bump * cos_v
    return re_val, im_val


def build_position_boxes(families, pos):
    bumps, phases = [], []
    for width, modulation in families:
        radius = width * width
        if abs(pos) >= radius:
            bumps.append((Fraction(0) - DELTA, Fraction(0) + DELTA))
        else:
            quotient = 1 - (pos / radius) ** 2
            bump = exact_exp(Fraction(-30) / quotient)
            bumps.append((bump - DELTA, bump + DELTA))
        cos_v, sin_v = exact_cos_sin(modulation * pos)
        phases.append(((cos_v - DELTA, cos_v + DELTA),
                       (sin_v - DELTA, sin_v + DELTA)))
    return bumps, phases


def real_literal(fr):
    num = f"({fr.numerator} : ℚ)" if fr.denominator == 1 \
        else f"({fr.numerator} : ℚ) / {fr.denominator}"
    return f"({num} : ℝ)"


def rect_literal(re_box, im_box):
    return "{{ reLo := {rl}, reHi := {rh}, imLo := {il}, imHi := {ih} }}".format(
        rl=real_literal(re_box[0]), rh=real_literal(re_box[1]),
        il=real_literal(im_box[0]), ih=real_literal(im_box[1]))


def complex_literal(re_, im_):
    return f"⟨{real_literal(re_)}, {real_literal(im_)}⟩"


def position_tag(index):
    return f"p{index:02d}"


def chain_term(hull, k):
    if k == FAMILIES - 1:
        return f"({hull} {k})"
    return f"(({hull} {k}).add {chain_term(hull, k + 1)})"


def wrap_rw(items):
    lines = []
    cur = "    rw ["
    for i, item in enumerate(items):
        piece = item + (", " if i < len(items) - 1 else "]")
        if len(cur) + len(piece) > 94:
            lines.append(cur.rstrip())
            cur = "      " + piece
        else:
            cur += piece
    lines.append(cur)
    return "\n".join(lines)


def family_hull_block(ch, tag, idx, hull_lit, coef_cap, coef_lit,
                      bump_lit, phase_lit):
    hull = f"hullRect2454{ch}{tag}"
    prod = ("(((ComplexRect2427.point ({cap} {i})).mul (bumpRect2453{t} {i}))"
            ".mul (phaseRect2453{t} {i}))").format(cap=coef_cap, t=tag, i=idx)
    return f"""theorem familyHull2454{ch}{tag}f{idx:02d}
    (hBump : ∀ k : Fin 30, (bumpRect2453{tag} k).Mem
      (widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ))
    (hPhase : ∀ k : Fin 30, (phaseRect2453{tag} k).Mem
      (Complex.exp (capMod2453 k * pos2453{tag} * Complex.I))) :
    ({hull} {idx}).Mem (externalFamilyValue2344 ({coef_cap} {idx})
      (capMod2453 {idx}) (storedWidth {idx} ^ 2) pos2453{tag}) := by
  have hc : ({hull} {idx}).reLo ≤ {prod}.reLo ∧
      {prod}.reHi ≤ ({hull} {idx}).reHi ∧
      ({hull} {idx}).imLo ≤ {prod}.imLo ∧
      {prod}.imHi ≤ ({hull} {idx}).imHi := by
    have hc1 : {coef_cap} {idx} = {coef_lit} := rfl
    have hc2 : bumpRect2453{tag} {idx} = {bump_lit} := rfl
    have hc3 : phaseRect2453{tag} {idx} = {phase_lit} := rfl
    have hc4 : {hull} {idx} = {hull_lit} := rfl
    rw [hc1, hc2, hc3, hc4]
    simp only [ComplexRect2427.mul, ComplexRect2427.point,
      RealInterval2429.mul, RealInterval2429.sub, RealInterval2429.add]
    norm_num
  exact mem_of_rect_subset_2454
    (familyRect2453{ch}{tag}_mem {idx} (hBump {idx}) (hPhase {idx}))
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2"""


def position_block(ch, tag, hulls, hull_lits, bumps, phases, coefficients,
                   n_literal):
    coef_cap = "capBaseCoef2453" if ch == "Base" else "capCorrCoef2453"
    hull = f"hullRect2454{ch}{tag}"
    chain = f"chainRect2454{ch}{tag}"
    parts = []
    arr_lines = ",\n    ".join(hull_lits)
    parts.append(
        f"noncomputable def {hull} : Fin 30 → ComplexRect2427 :=\n"
        f"  ![{arr_lines}]")
    for k in range(FAMILIES):
        coef_re, coef_im = coefficients[k]
        bump_lit = rect_literal(bumps[k], (Fraction(0), Fraction(0)))
        phase_lit = rect_literal(phases[k][0], phases[k][1])
        parts.append(family_hull_block(ch, tag, k, hull_lits[k], coef_cap,
                                       complex_literal(coef_re, coef_im),
                                       bump_lit, phase_lit))
    leaves = f"(familyHull2454{ch}{tag}f{FAMILIES - 1:02d} hBump hPhase)"
    for k in range(FAMILIES - 2, -1, -1):
        leaves = (f"(ComplexRect2427.mem_add (familyHull2454{ch}{tag}f{k:02d} "
                  f"hBump hPhase) {leaves})")

    def sum_tree(k):
        term = (f"externalFamilyValue2344 ({coef_cap} {k}) (capMod2453 {k})"
                f" (storedWidth {k} ^ 2) pos2453{tag}")
        return term if k == FAMILIES - 1 else f"({term} + {sum_tree(k + 1)})"
    parts.append(
        f"noncomputable def {chain} : ComplexRect2427 :=\n"
        f"  {chain_term(hull, 0)}")
    parts.append(f"""theorem sumMem2454{ch}{tag}
    (hBump : ∀ k : Fin 30, (bumpRect2453{tag} k).Mem
      (widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ))
    (hPhase : ∀ k : Fin 30, (phaseRect2453{tag} k).Mem
      (Complex.exp (capMod2453 k * pos2453{tag} * Complex.I))) :
    {chain}.Mem (correctedPhysical {coef_cap} capMod2453 pos2453{tag}) := by
  rw [← externalPhysical2344_eq_correctedPhysical]
  unfold externalPhysical2344
  rw [fin30_sum_univ_chain_2454
    (fun i => externalFamilyValue2344 ({coef_cap} i) (capMod2453 i)
      (storedWidth i ^ 2) pos2453{tag})]
  exact {leaves}""")
    peel_lines = "\n".join(
        f"    have hp{k} : {hull} {k} = {hull_lits[k]} := rfl"
        for k in range(FAMILIES))
    rw_block = wrap_rw([chain] + [f"hp{k}" for k in range(FAMILIES)])
    parts.append(f"""theorem nodeNorm2454{ch}{tag}
    (hBump : ∀ k : Fin 30, (bumpRect2453{tag} k).Mem
      (widthBump (storedWidth k ^ 2) pos2453{tag} : ℂ))
    (hPhase : ∀ k : Fin 30, (phaseRect2453{tag} k).Mem
      (Complex.exp (capMod2453 k * pos2453{tag} * Complex.I))) :
    ‖correctedPhysical {coef_cap} capMod2453 pos2453{tag}‖ ≤ {n_literal} := by
  refine le_trans
    (b := max |{chain}.reLo| |{chain}.reHi| +
      max |{chain}.imLo| |{chain}.imHi|) ?_ ?_
  · exact norm_le_of_rect_mem_2453 {chain}
      (sumMem2454{ch}{tag} hBump hPhase)
  · -- goal: max |chain.reLo| |chain.reHi| + max |chain.imLo| |chain.imHi| ≤ N
{peel_lines}
{rw_block}
    simp only [ComplexRect2427.add]
    norm_num""")
    return "\n\n".join(parts)


def module_text(header, body):
    return f"""{header}

set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

{body}

end ConnesWeilRH.Dev
"""


HEADER = """import ConnesWeilRH.Dev.C1RouteAOwnerNodeNormImport2453
import ConnesWeilRH.Dev.C1RouteANormBridge2453
import ConnesWeilRH.Dev.C1RouteANormBridge2454

/-  2454: Lean node-norm bounds for the 2453 import positions.  For each
of the 11 positions and both channels: a literal outer-hull array (bound
to results/2454_owner_node_norm_bound.json by the independent pin), per
family a containment theorem into the hull, a chain rectangle whose
membership transports the 30-term owner sum, and the node-norm theorem
||correctedPhysical ...|| <= N with N an exact rational.  The hull and
N literals are machine-generated; the long-line linter is disabled for
this file only.  -/"""


def main():
    families, base, corr, capture = load_owner()
    positions = load_positions()
    art_2453 = json.loads(ART_2453.read_text())
    sum_2453 = art_2453["sum_boxes_and_bounds"]

    checks, failures = [], []
    cross_mismatches = []
    blocks = []
    n_records = {}
    hull_records = {}
    for idx, pos in enumerate(positions):
        tag = position_tag(idx)
        bumps, phases = build_position_boxes(families, pos)
        for channel, coefficients in (("base", base), ("corr", corr)):
            ch = channel.capitalize()
            hulls = []
            hull_lits = []
            re_box_sum = (Fraction(0), Fraction(0))
            im_box_sum = (Fraction(0), Fraction(0))
            for k in range(FAMILIES):
                coef_re, coef_im = coefficients[k]
                rr, ii = composed_hull(coef_re, coef_im, bumps[k], phases[k])
                radius = families[k][0] * families[k][0]
                if abs(pos) >= radius:
                    bump = Fraction(0)
                else:
                    bump = exact_exp(Fraction(-30) /
                                     (1 - (pos / radius) ** 2))
                cos_v, sin_v = exact_cos_sin(families[k][1] * pos)
                re_ref, im_ref = reference_term(coef_re, coef_im, bump,
                                                cos_v, sin_v)
                ok = rr[0] <= re_ref <= rr[1] and ii[0] <= im_ref <= ii[1]
                checks.append({"channel": channel, "family": k, "tag": tag,
                               "contains_reference": ok})
                if not ok:
                    failures.append(f"{channel}[{k}]@{tag}")
                re_box_sum = interval_add(re_box_sum, rr)
                im_box_sum = interval_add(im_box_sum, ii)
                hulls.append((rr, ii))
                hull_lits.append(rect_literal(rr, ii))
            ref = sum_2453.get(f"{channel}_{tag}")
            if ref is None or \
                    ref["re"] != [str(re_box_sum[0]), str(re_box_sum[1])] or \
                    ref["im"] != [str(im_box_sum[0]), str(im_box_sum[1])]:
                cross_mismatches.append(f"{channel}_{tag}")
            mre = max(abs(re_box_sum[0]), abs(re_box_sum[1]))
            mim = max(abs(im_box_sum[0]), abs(im_box_sum[1]))
            n_val = mre + mim
            n_records[f"{channel}_{tag}"] = str(n_val)
            hull_records[f"{channel}_{tag}"] = hull_lits
            blocks.append(position_block(ch, tag, hulls, hull_lits, bumps,
                                         phases, coefficients,
                                         real_literal(n_val)))

    body = "\n\n".join(blocks)
    LEAN_OUT.write_text(module_text(HEADER, body), encoding="utf-8")

    audit_names = ["mem_of_rect_subset_2454"]
    for idx in range(11):
        tag = position_tag(idx)
        for channel in ("Base", "Corr"):
            audit_names.append(f"nodeNorm2454{channel}{tag}")
    AUDIT_OUT.write_text(module_text(
        "import ConnesWeilRH.Dev.C1RouteAOwnerNodeNormBound2454",
        "\n".join(f"#print axioms {name}" for name in audit_names)),
        encoding="utf-8")

    artifact = {
        "record": 2454,
        "verdict": "OWNER-NODE-NORM-BOUND-COMPLETE" if not failures
        and not cross_mismatches else "OWNER-NODE-NORM-BOUND-FAILURES",
        "scope": ("Lean node-norm bounds ||correctedPhysical|| <= N at the "
                  "11 2453 positions, both channels, through hull literals "
                  "+ mem_of_rect_subset_2454 + the 2453 bridge; no strip "
                  "norm, no quadrature import, no producer GO, no RH claim"),
        "positions": [str(p) for p in positions],
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "certificate_sha256": hashlib.sha256(CERT.read_bytes()).hexdigest(),
        "upstream_2453_sha256": art_2453["lean_module_sha256"],
        "producer_source_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "lean_module_sha256": hashlib.sha256(
            LEAN_OUT.read_bytes()).hexdigest(),
        "delta": f"{DELTA.numerator}/{DELTA.denominator}",
        "dps_work": DPS_WORK,
        "containment_checks": len(checks),
        "containment_failures": failures,
        "cross_record_2453_mismatches": cross_mismatches,
        "n_bounds": n_records,
        "hull_literals": hull_records,
        "producer_go": False,
        "rh_claim": False,
    }
    ARTIFACT_OUT.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")

    print(json.dumps({
        "verdict": artifact["verdict"],
        "checks": len(checks),
        "failures": failures[:5],
        "cross_mismatches": cross_mismatches[:5],
        "lean_module_bytes": LEAN_OUT.stat().st_size,
    }, indent=2))


if __name__ == "__main__":
    main()
