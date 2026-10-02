"""2452: first actual-owner point import through the hypothesis-class door.

Generates, at the evaluation point x0 = 1/2, the per-family factor
rectangles of the captured owner (2275) in the 2427/2433 Lean shapes:

    externalFamilyValue2344 c_k m_k (storedWidth k)^2 x0
      = c_k * widthBump (storedWidth k)^2 x0 * exp(i m_k x0)
      = [coefficient point box] x [bump box] x [phase box],

emits the Lean literal module C1RouteAOwnerPointImport2452.lean (captured
coefficients/modulations as exact dyadic literals, bump/phase rectangles
as exact rational literals), verifies the composed four-corner hull
contains a dps-120 reference of every family term and of the full
30-family sum, and writes the artifact.  The bump/phase containment
fields stay Lean hypotheses; the pin script binds the literals to this
artifact.  Scope: one point, one import exercise; no strip norm, no
producer GO, no RH claim.
"""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
LEAN_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPointImport2452.lean"
AUDIT_OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPointImport2452Audit.lean"
ARTIFACT_OUT = ROOT / "results/2452_owner_point_import.json"

DPS_WORK = 90
DPS_REF = 120
DELTA = Fraction(1, 2 ** 200)   # outward box margin (exact, ~6.2e-61)
POSITION = Fraction(1, 2)


def load_owner():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(Fraction(float.fromhex(width)), Fraction(float.fromhex(modulation)))
                for width, modulation in capture["families_hex"]]
    base = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["base_hex"]]
    corr = [(Fraction(float.fromhex(re_)), Fraction(float.fromhex(im_)))
            for re_, im_ in capture["corr_hex"]]
    for name, coefficients in (("base", base), ("corr", corr)):
        flat = np.asarray([complex(float(re_), float(im_)) for re_, im_ in coefficients],
                          dtype=np.complex128)
        digest = hashlib.md5(flat.tobytes()).hexdigest()
        if digest != capture[name + "_md5"]:
            raise ValueError("stored coefficient hash mismatch: " + name)
    return families, base, corr, capture


def mpf_to_fraction(v):
    sign, man, exp, _bc = mp.mpf(v)._mpf_
    if man == 0:
        return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f


def exact_exp(fraction):
    """exp of an exact rational at dps 90, returned as an exact Fraction."""
    mp.mp.dps = DPS_WORK
    approx = mp.exp(mp.mpf(fraction.numerator) / mp.mpf(fraction.denominator))
    return mpf_to_fraction(approx)


def exact_cos_sin(fraction):
    mp.mp.dps = DPS_WORK
    x = mp.mpf(fraction.numerator) / mp.mpf(fraction.denominator)
    return mpf_to_fraction(mp.cos(x)), mpf_to_fraction(mp.sin(x))


def interval_mul(a, b):
    """Exact four-corner interval product ((lo, hi) pairs of Fractions)."""
    corners = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(corners), max(corners)


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def point_interval(x):
    return x, x


def rat_literal(fr):
    return str(fr.numerator) if fr.denominator == 1 \
        else f"({fr.numerator} / {fr.denominator})"


def real_literal(fr):
    num = f"({fr.numerator} : ℚ)" if fr.denominator == 1 \
        else f"({fr.numerator} : ℚ) / {fr.denominator}"
    return f"({num} : ℝ)"


def build_certificates(families):
    """Per family: bump box (real), phase boxes (re/im), exact fractions."""
    bumps, phases = [], []
    for width, modulation in families:
        radius = width * width
        quotient = 1 - (POSITION / radius) ** 2
        if quotient <= 0:
            raise ValueError("position outside family support")
        bump = exact_exp(Fraction(-30) / quotient)
        bumps.append((bump - DELTA, bump + DELTA))
        cos_v, sin_v = exact_cos_sin(modulation * POSITION)
        phases.append(((cos_v - DELTA, cos_v + DELTA),
                       (sin_v - DELTA, sin_v + DELTA)))
    return bumps, phases


def composed_hull(coef_re, coef_im, bump_box, phase_boxes):
    """Exact four-corner hull of c * bump * phase (complex)."""
    coef_re_i, coef_im_i = point_interval(coef_re), point_interval(coef_im)
    phase_re_i, phase_im_i = phase_boxes
    rr = interval_sub(interval_mul(coef_re_i, interval_mul(bump_box, phase_re_i)),
                      interval_mul(coef_im_i, interval_mul(bump_box, phase_im_i)))
    ii = interval_add(interval_mul(coef_re_i, interval_mul(bump_box, phase_im_i)),
                      interval_mul(coef_im_i, interval_mul(bump_box, phase_re_i)))
    return rr, ii


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def reference_term(coef_re, coef_im, bump, cos_v, sin_v):
    """Exact rational product of the box-centre values."""
    re_val = coef_re * bump * cos_v - coef_im * bump * sin_v
    im_val = coef_re * bump * sin_v + coef_im * bump * cos_v
    return re_val, im_val


def lean_module_text(families, base, corr, bumps, phases):
    coef_lines_b = ",\n    ".join(
        f"⟨{real_literal(re_)}, {real_literal(im_)}⟩" for re_, im_ in base)
    coef_lines_c = ",\n    ".join(
        f"⟨{real_literal(re_)}, {real_literal(im_)}⟩" for re_, im_ in corr)
    mod_lines = ",\n    ".join(real_literal(mod) for _, mod in families)
    bump_lines = ",\n    ".join(
        "{{ reLo := {lo}, reHi := {hi}, imLo := ((0 : ℚ) : ℝ),"
        " imHi := ((0 : ℚ) : ℝ) }}".format(
            lo=real_literal(lo), hi=real_literal(hi))
        for lo, hi in bumps)
    phase_lines = ",\n    ".join(
        "{{ reLo := {rl}, reHi := {rh}, imLo := {il}, imHi := {ih} }}".format(
            rl=real_literal(re_box[0]), rh=real_literal(re_box[1]),
            il=real_literal(im_box[0]), ih=real_literal(im_box[1]))
        for re_box, im_box in phases)

    return f"""import ConnesWeilRH.Dev.C1RouteAOwnerTermInterface

/- 2452: first actual-owner point import through the hypothesis-class
door.  The coefficient, modulation and rectangle literals below are exact
dyadic/rational bindings of the 2275 capture at the evaluation point
x0 = 1/2; they are bound to `results/2452_owner_point_import.json` by the
independent pin check.  The bump and phase containment fields are the
2333 hypothesis class; the composition and the 30-family sum are proved
in Lean through the 2437 factor interface and the 2436 owner consumer.
The exact-rational literals are machine-generated; the long-line linter
is disabled for this file only. -/

set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def capBaseCoef2452 : Fin 30 → ℂ :=
  ![{coef_lines_b}]

noncomputable def capCorrCoef2452 : Fin 30 → ℂ :=
  ![{coef_lines_c}]

noncomputable def capMod2452 : Fin 30 → ℝ :=
  ![{mod_lines}]

noncomputable def bumpRect2452 : Fin 30 → ComplexRect2427 :=
  ![{bump_lines}]

noncomputable def phaseRect2452 : Fin 30 → ComplexRect2427 :=
  ![{phase_lines}]

noncomputable def baseCoefValue2452 (k : Fin 30) : DirectedComplexValue2433 :=
  ⟨capBaseCoef2452 k, ComplexRect2427.point (capBaseCoef2452 k),
    ComplexRect2427.point_mem _⟩

noncomputable def corrCoefValue2452 (k : Fin 30) : DirectedComplexValue2433 :=
  ⟨capCorrCoef2452 k, ComplexRect2427.point (capCorrCoef2452 k),
    ComplexRect2427.point_mem _⟩

noncomputable def bumpValue2452 (k : Fin 30)
    (h : (bumpRect2452 k).Mem
      (widthBump (storedWidth k ^ 2) (1 / 2 : ℝ) : ℂ)) :
    DirectedComplexValue2433 :=
  ⟨(widthBump (storedWidth k ^ 2) (1 / 2 : ℝ) : ℂ), bumpRect2452 k, h⟩

noncomputable def phaseValue2452 (k : Fin 30)
    (h : (phaseRect2452 k).Mem
      (Complex.exp (capMod2452 k * (1 / 2 : ℝ) * Complex.I))) :
    DirectedComplexValue2433 :=
  ⟨Complex.exp (capMod2452 k * (1 / 2 : ℝ) * Complex.I),
    phaseRect2452 k, h⟩

theorem familyRect2452_mem_base (k : Fin 30)
    (hBump : (bumpRect2452 k).Mem
      (widthBump (storedWidth k ^ 2) (1 / 2 : ℝ) : ℂ))
    (hPhase : (phaseRect2452 k).Mem
      (Complex.exp (capMod2452 k * (1 / 2 : ℝ) * Complex.I))) :
    (((baseCoefValue2452 k).product (bumpValue2452 k hBump)).product
      (phaseValue2452 k hPhase)).rectangle.Mem
      (externalFamilyValue2344 (capBaseCoef2452 k) (capMod2452 k)
        (storedWidth k ^ 2) (1 / 2 : ℝ)) :=
  externalFamilyValue_mem_of_factor_cert2437 _ _ _ _ (by
    simp only [DirectedComplexValue2433.product, baseCoefValue2452,
      bumpValue2452, phaseValue2452]
    rw [externalFamilyValue2344_eq_familyTerm, Complex.ofReal_mul])

theorem familyRect2452_mem_corr (k : Fin 30)
    (hBump : (bumpRect2452 k).Mem
      (widthBump (storedWidth k ^ 2) (1 / 2 : ℝ) : ℂ))
    (hPhase : (phaseRect2452 k).Mem
      (Complex.exp (capMod2452 k * (1 / 2 : ℝ) * Complex.I))) :
    (((corrCoefValue2452 k).product (bumpValue2452 k hBump)).product
      (phaseValue2452 k hPhase)).rectangle.Mem
      (externalFamilyValue2344 (capCorrCoef2452 k) (capMod2452 k)
        (storedWidth k ^ 2) (1 / 2 : ℝ)) :=
  externalFamilyValue_mem_of_factor_cert2437 _ _ _ _ (by
    simp only [DirectedComplexValue2433.product, corrCoefValue2452,
      bumpValue2452, phaseValue2452]
    rw [externalFamilyValue2344_eq_familyTerm, Complex.ofReal_mul])

theorem correctedPhysical_base_point_mem_2452
    (hBump : ∀ k : Fin 30, (bumpRect2452 k).Mem
      (widthBump (storedWidth k ^ 2) (1 / 2 : ℝ) : ℂ))
    (hPhase : ∀ k : Fin 30, (phaseRect2452 k).Mem
      (Complex.exp (capMod2452 k * (1 / 2 : ℝ) * Complex.I))) :
    (ComplexRect2427.sumFinset
      (fun k => (((baseCoefValue2452 k).product (bumpValue2452 k (hBump k))).product
        (phaseValue2452 k (hPhase k))).rectangle) Finset.univ).Mem
      (correctedPhysical capBaseCoef2452 capMod2452 (1 / 2 : ℝ)) :=
  correctedPhysical_mem_of_family_rect2436 capBaseCoef2452 capMod2452
    (1 / 2 : ℝ) _ (fun k => familyRect2452_mem_base k (hBump k) (hPhase k))

theorem correctedPhysical_corr_point_mem_2452
    (hBump : ∀ k : Fin 30, (bumpRect2452 k).Mem
      (widthBump (storedWidth k ^ 2) (1 / 2 : ℝ) : ℂ))
    (hPhase : ∀ k : Fin 30, (phaseRect2452 k).Mem
      (Complex.exp (capMod2452 k * (1 / 2 : ℝ) * Complex.I))) :
    (ComplexRect2427.sumFinset
      (fun k => (((corrCoefValue2452 k).product (bumpValue2452 k (hBump k))).product
        (phaseValue2452 k (hPhase k))).rectangle) Finset.univ).Mem
      (correctedPhysical capCorrCoef2452 capMod2452 (1 / 2 : ℝ)) :=
  correctedPhysical_mem_of_family_rect2436 capCorrCoef2452 capMod2452
    (1 / 2 : ℝ) _ (fun k => familyRect2452_mem_corr k (hBump k) (hPhase k))

end ConnesWeilRH.Dev
"""


def audit_module_text():
    return """import ConnesWeilRH.Dev.C1RouteAOwnerPointImport2452

namespace ConnesWeilRH.Dev

#print axioms familyRect2452_mem_base
#print axioms familyRect2452_mem_corr
#print axioms correctedPhysical_base_point_mem_2452
#print axioms correctedPhysical_corr_point_mem_2452

end ConnesWeilRH.Dev
"""


def main():
    families, base, corr, capture = load_owner()
    bumps, phases = build_certificates(families)

    checks, failures = [], []
    sum_box = (point_interval(Fraction(0)), point_interval(Fraction(0)))
    for channel, coefficients in (("base", base), ("corr", corr)):
        for k in range(30):
            coef_re, coef_im = coefficients[k]
            rr, ii = composed_hull(coef_re, coef_im, bumps[k], phases[k])
            bump = exact_exp(Fraction(-30) /
                             (1 - (POSITION / (families[k][0] * families[k][0])) ** 2))
            cos_v, sin_v = exact_cos_sin(families[k][1] * POSITION)
            re_ref, im_ref = reference_term(coef_re, coef_im, bump, cos_v, sin_v)
            ok = rr[0] <= re_ref <= rr[1] and ii[0] <= im_ref <= ii[1]
            checks.append({"channel": channel, "family": k,
                           "contains_reference": ok,
                           "margin_re": float(min(re_ref - rr[0], rr[1] - re_ref)),
                           "margin_im": float(min(im_ref - ii[0], ii[1] - im_ref))})
            if not ok:
                failures.append(f"{channel}[{k}]")
            if channel == "base":
                sum_box = (interval_add(sum_box[0], rr),
                           interval_add(sum_box[1], ii))

    lean_text = lean_module_text(families, base, corr, bumps, phases)
    LEAN_OUT.write_text(lean_text, encoding="utf-8")
    AUDIT_OUT.write_text(audit_module_text(), encoding="utf-8")

    def frac_str(fr):
        return f"{fr.numerator}/{fr.denominator}"

    artifact = {
        "record": 2452,
        "verdict": "OWNER-POINT-IMPORT-CERTIFICATES-COMPLETE" if not failures
        else "OWNER-POINT-IMPORT-CONTAINMENT-FAILURES",
        "scope": ("first actual-owner point import exercise at x0 = 1/2 "
                  "through the 2433/2437/2436 hypothesis-class door; one "
                  "point, no strip norm, no producer GO, no RH claim"),
        "position_num": "1/2",
        "capture_md5s": {"base": capture["base_md5"], "corr": capture["corr_md5"]},
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "producer_source_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "lean_module_sha256": hashlib.sha256(
            LEAN_OUT.read_bytes()).hexdigest(),
        "delta": frac_str(DELTA),
        "dps_work": DPS_WORK,
        "containment_checks": checks,
        "containment_failures": failures,
        "base_sum_box": {
            "re": [frac_str(x) for x in sum_box[0]],
            "im": [frac_str(x) for x in sum_box[1]],
        },
        "bump_boxes": [{"re": [frac_str(lo), frac_str(hi)], "im": ["0/1", "0/1"]}
                       for lo, hi in bumps],
        "phase_boxes": [{"re": [frac_str(re_box[0]), frac_str(re_box[1])],
                         "im": [frac_str(im_box[0]), frac_str(im_box[1])]}
                        for re_box, im_box in phases],
        "producer_go": False,
        "rh_claim": False,
    }
    ARTIFACT_OUT.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")

    print(json.dumps({
        "verdict": artifact["verdict"],
        "families_checked": len(checks),
        "failures": failures,
        "base_sum_box_re": [float(x) for x in sum_box[0]],
        "base_sum_box_im": [float(x) for x in sum_box[1]],
        "lean_module": str(LEAN_OUT.name),
    }, indent=2))


if __name__ == "__main__":
    main()
