"""2460 (producer brick 1): one-panel end-to-end owner sample.

First instantiation of the 2459 attachment doors with ACTUAL owner
data, per the 2456 ruling: coefficient BALLS from the 2338 exact
interpolation repair (midpoint frozen, [lo, hi] box kept), family
parameters (width -> radius, modulation) from the frozen 2275 capture
(same source the 2342/2343 protocol pins), on the production-grid
panel of the 2455 floor (N = 120001, R = 65536/10000) containing
x = 1/4.

Key design point: the sample is HYPOTHESIS-FREE.  Every box endpoint
is a closed-form Lean expression - bump box [0, exp(-30/q(x0))] by
the nonneg lemma + antitone sup-at-left-endpoint, phase boxes
cos(mid) +- rho by the certified midpoint-box lemma - so Lean
verifies the whole chain by rational arithmetic plus the 2459 box
shape lemmas.  No transcendental facts, no delta outward rounding.

Emits ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460.lean and
results/2460_owner_panel_sample.json.  Diagnostic sample: no trapezoid
sum T, no zeta, no strip norm discharged, no GO, no RH claim.
"""
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp

sys.set_int_max_str_digits(400000)

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT_JSON = ROOT / "results/2460_owner_panel_sample.json"
OUT_LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460.lean"

DPS = 90
FAMILIES = 30
N_GRID = 120001
RADIUS_R = Fraction(65536, 10000)   # exact stand-in for the ~6.5536 owner R
X_TARGET = Fraction(1, 4)
SAMPLES = 5


def load_inputs():
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    rows = repair["coefficient_rows"]
    assert len(rows) == FAMILIES
    fams = []
    for k, row in enumerate(rows):
        assert row["index"] == k
        width = Fraction(float.fromhex(capture["families_hex"][k][0]))
        mod = Fraction(float.fromhex(capture["families_hex"][k][1]))
        re_lo = Fraction(row["ideal_base_coefficient"]["real"]["lower_exact"])
        re_hi = Fraction(row["ideal_base_coefficient"]["real"]["upper_exact"])
        im_lo = Fraction(row["ideal_base_coefficient"]["imag"]["lower_exact"])
        im_hi = Fraction(row["ideal_base_coefficient"]["imag"]["upper_exact"])
        assert re_lo <= re_hi and im_lo <= im_hi
        fams.append({
            "width": width, "radius": width * width, "mod": mod,
            "re_lo": re_lo, "re_hi": re_hi, "im_lo": im_lo, "im_hi": im_hi,
            "re_mid": (re_lo + re_hi) / 2, "im_mid": (im_lo + im_hi) / 2,
        })
    pins = {
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "repair_capture_sha256_pinned": repair["capture_sha256"],
        "repair_status": repair["status"],
        "precision_bits": repair["precision_bits"],
    }
    return fams, pins


def grid_panel():
    h = 2 * RADIUS_R / (N_GRID - 1)
    j = int(((X_TARGET + RADIUS_R) / h).__floor__())
    x0 = -RADIUS_R + j * h
    x1 = x0 + h
    assert x0 <= X_TARGET < x1, "panel must contain 1/4"
    assert x0 > 0, "sample panel is the positive interior half-line"
    return x0, x1, h


def mpf_to_fraction(v):
    sign, man, exp, _ = mp.mpf(v)._mpf_
    if man == 0:
        return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f


def exact(fn, fr):
    mp.mp.dps = DPS
    return mpf_to_fraction(fn(mp.mpf(fr.numerator) / mp.mpf(fr.denominator)))


def imul(a, b):
    c = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(c), max(c)


def iadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def isub(a, b):
    return a[0] - b[1], a[1] - b[0]


def rect_mul(a, b):
    """Mirror of RealInterval2429.mul + ComplexRect2427.mul."""
    ar, ai = a
    br, bi = b
    arr = imul(ar, br)
    aibi = imul(ai, bi)
    arbi = imul(ar, bi)
    aibr = imul(ai, br)
    re = isub(arr, aibi)
    im = iadd(arbi, aibr)
    return re, im


def truth_bump(radius, x):
    if abs(x) < radius:
        q = 1 - (x / radius) ** 2
        return exact(mp.exp, Fraction(-30) / q)
    return Fraction(0)


def truth_value(f, x):
    b = truth_bump(f["radius"], x)
    c, s = exact(mp.cos, f["mod"] * x), exact(mp.sin, f["mod"] * x)
    re = f["re_mid"] * b * c - f["im_mid"] * b * s
    im = f["re_mid"] * b * s + f["im_mid"] * b * c
    return re, im


def q_lit(f):
    if f.denominator == 1:
        return f"({f.numerator} : ℚ)"
    return f"({f.numerator} / {f.denominator} : ℚ)"


def r_lit(f):
    return f"(({f.numerator} / {f.denominator} : ℚ) : ℝ)" \
        if f.denominator != 1 else f"(({f.numerator} : ℚ) : ℝ)"


PREAMBLE = r"""import ConnesWeilRH.Dev.C1RouteAQuadratureAttachment2459

/-  2460: one-panel end-to-end owner sample through the 2459
attachment doors - the first producer instantiation with actual
owner data (2338 coefficient balls, 2275 frozen family parameters,
2455 production-grid panel containing 1/4).  HYPOTHESIS-FREE: every
box endpoint is a closed-form expression; Lean verifies by rational
arithmetic plus the 2459/2460 box shape lemmas.  Sample scope only:
no trapezoid sum, no zeta, no strip norm discharged, no GO, no RH
claim.  Generated by scripts/routea_owner_panel_sample_2460.py;
regenerate, do not hand-edit.  -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false
set_option maxRecDepth 32768

theorem widthBump_nonneg_2460 (radius x : ℝ) :
    0 ≤ C1RouteAOwnerScaleAudit.widthBump radius x := by
  by_cases h : |x| < radius
  · simp only [C1RouteAOwnerScaleAudit.widthBump, if_pos h]
    exact le_of_lt (Real.exp_pos _)
  · simp [C1RouteAOwnerScaleAudit.widthBump, h]

theorem widthBump_sup_left_2460 {radius x0 x : ℝ} (hx0 : 0 ≤ x0)
    (hx0r : x0 < radius) (hxpos : 0 ≤ x) (hxr : |x| < radius) (hle : x0 ≤ x) :
    C1RouteAOwnerScaleAudit.widthBump radius x ≤
      C1RouteAOwnerScaleAudit.widthBump radius x0 :=
  widthBump_antitone_right_2459 radius ⟨hx0, hx0r⟩ ⟨hxpos, by
    exact (abs_lt.mp hxr).2⟩ hle

"""


def fam_defs(k, f, alive, m_nonneg):
    """Emit the per-family box defs referenced by famPanel{k}_2460.

    Boxes live in defs (not inlined in theorem statements) because
    structInst notation breaks when a continuation field line is
    outdented relative to the '{' column; defs keep every continuation
    line indented past the brace and keep statements short.
    """
    m, rad = f"mod{k}_2460", f"rad{k}_2460"
    re_lo, re_hi = r_lit(f["re_lo"]), r_lit(f["re_hi"])
    im_lo, im_hi = r_lit(f["im_lo"]), r_lit(f["im_hi"])
    lo_t, hi_t = ("X0_2460", "X1_2460") if m_nonneg else ("X1_2460", "X0_2460")
    arg_mid = f"(({m} * {lo_t} + {m} * {hi_t}) / 2)"
    arg_rho = f"({m} * {hi_t} - {m} * {lo_t}) / 2"
    bump = (f"Real.exp ((-(30 : ℝ)) / (1 - (X0_2460 / {rad}) ^ 2))"
            if alive else "(0 : ℝ)")
    return f"""def coefRect{k}_2460 : ComplexRect2427 :=
  {{ reLo := {re_lo},
    reHi := {re_hi},
    imLo := {im_lo},
    imHi := {im_hi} }}

noncomputable def bumpBox{k}_2460 : ComplexRect2427 :=
  {{ reLo := (0 : ℝ), reHi := {bump},
    imLo := (0 : ℝ), imHi := (0 : ℝ) }}

noncomputable def phaseBox{k}_2460 : ComplexRect2427 :=
  {{ reLo := Real.cos {arg_mid} - {arg_rho},
    reHi := Real.cos {arg_mid} + {arg_rho},
    imLo := Real.sin {arg_mid} - {arg_rho},
    imHi := Real.sin {arg_mid} + {arg_rho} }}

"""


def fam_lemma(k, f, alive, m_nonneg):
    """Emit one family's panel-membership theorem over the box defs."""
    m, rad = f"mod{k}_2460", f"rad{k}_2460"
    lo_t, hi_t = ("X0_2460", "X1_2460") if m_nonneg else ("X1_2460", "X0_2460")
    arg_mid = f"(({m} * {lo_t} + {m} * {hi_t}) / 2)"
    arg_rho = f"({m} * {hi_t} - {m} * {lo_t}) / 2"
    if m_nonneg:
        sign_haves = (
            f"  have hm0 : (0 : ℝ) ≤ {m} := by norm_num [{m}]\n"
            f"  have h01 : {m} * X0_2460 ≤ {m} * X1_2460 :=\n"
            f"    mul_le_mul_of_nonneg_left hX01 hm0\n")
        mem_l = "by nlinarith [hx.1, hm0]"
        mem_h = "by nlinarith [hx.2, hm0]"
    else:
        sign_haves = (
            f"  have hmn : {m} ≤ 0 := by norm_num [{m}]\n"
            f"  have h01 : {m} * X1_2460 ≤ {m} * X0_2460 := by\n"
            f"    nlinarith [hX01, hmn]\n")
        mem_l = "by nlinarith [hx.2, hmn]"
        mem_h = "by nlinarith [hx.1, hmn]"
    if alive:
        hbm = f"""  have hbm : bumpBox{k}_2460.Mem
      (C1RouteAOwnerScaleAudit.widthBump {rad} x : ℝ) := by
    by_cases hin : |x| < {rad}
    · have hX0pos : (0 : ℝ) ≤ X0_2460 := by norm_num [X0_2460]
      have hX0rad : X0_2460 < {rad} := by norm_num [X0_2460, {rad}]
      have hX0in : |X0_2460| < {rad} := by
        rw [abs_of_nonneg hX0pos]; exact hX0rad
      have hsup := widthBump_sup_left_2460 (radius := {rad})
        (x0 := X0_2460) hX0pos hX0rad (le_trans hX0pos hx.1) hin hx.1
      have hX0b : C1RouteAOwnerScaleAudit.widthBump {rad} X0_2460
          = bumpBox{k}_2460.reHi := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hX0in, bumpBox{k}_2460]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [bumpBox{k}_2460, Complex.ofReal_re] using
          widthBump_nonneg_2460 {rad} x
      · have h2 : C1RouteAOwnerScaleAudit.widthBump {rad} x
            ≤ bumpBox{k}_2460.reHi := le_trans hsup (le_of_eq hX0b)
        simpa [bumpBox{k}_2460, Complex.ofReal_re] using h2
    · have hb0 : C1RouteAOwnerScaleAudit.widthBump {rad} x = 0 := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hin]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [bumpBox{k}_2460, Complex.ofReal_re, hb0] using le_refl 0
      · simpa [bumpBox{k}_2460, Complex.ofReal_re, hb0] using
          le_of_lt (Real.exp_pos _)
"""
    else:
        hbm = f"""  have hbm : bumpBox{k}_2460.Mem
      (C1RouteAOwnerScaleAudit.widthBump {rad} x : ℝ) := by
    by_cases hin : |x| < {rad}
    · exfalso
      have hge : {rad} ≤ |x| :=
        le_trans (le_trans (by norm_num [X0_2460, {rad}]) hx.1)
          (le_abs_self x)
      exact absurd hin (not_lt_of_ge hge)
    · refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [bumpBox{k}_2460, Complex.ofReal_re] using
          widthBump_nonneg_2460 {rad} x
      · simpa [bumpBox{k}_2460, Complex.ofReal_re] using
          widthBump_nonneg_2460 {rad} x
"""
    body = f"""theorem famPanel{k}_2460 (x : ℝ) (hx : x ∈ Set.Icc X0_2460 X1_2460) :
    (ComplexRect2427.mul
      (ComplexRect2427.mul coefRect{k}_2460 bumpBox{k}_2460)
      phaseBox{k}_2460).Mem
      (externalFamilyValue2344 coef{k}_2460 {m} {rad} x) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  have hcoef : coefRect{k}_2460.Mem coef{k}_2460 := by
    constructor <;> norm_num [coefRect{k}_2460, coef{k}_2460]
  have hX01 : X0_2460 ≤ X1_2460 := by norm_num [X0_2460, X1_2460]
{sign_haves}{hbm}  have hph : phaseBox{k}_2460.Mem
      (Complex.exp (({m} * x : ℝ) * Complex.I)) := by
    have hre : (Complex.exp (({m} * x : ℝ) * Complex.I)).re
        = Real.cos ({m} * x) := by
      rw [Complex.exp_re]; simp
    have him : (Complex.exp (({m} * x : ℝ) * Complex.I)).im
        = Real.sin ({m} * x) := by
      rw [Complex.exp_im]; simp
    have hlip : |Real.cos ({m} * x) - Real.cos {arg_mid}| ≤ {arg_rho} := by
      refine cos_midpoint_box_2459 h01 ⟨{mem_l}, {mem_h}⟩
    have hsli : |Real.sin ({m} * x) - Real.sin {arg_mid}| ≤ {arg_rho} := by
      refine sin_midpoint_box_2459 h01 ⟨{mem_l}, {mem_h}⟩
    obtain ⟨hclo, hchi⟩ := abs_le.mp hlip
    obtain ⟨hslo, hshi⟩ := abs_le.mp hsli
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]; simp only [phaseBox{k}_2460]; linarith
    · rw [hre]; simp only [phaseBox{k}_2460]; linarith
    · rw [him]; simp only [phaseBox{k}_2460]; linarith
    · rw [him]; simp only [phaseBox{k}_2460]; linarith
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul hcoef hbm) hph
"""
    return body

def main():
    fams, pins = load_inputs()
    x0, x1, h = grid_panel()
    checks = []
    fam_out = []
    sum_re = (Fraction(0), Fraction(0))
    sum_im = (Fraction(0), Fraction(0))
    for k, f in enumerate(fams):
        alive = f["radius"] > x0
        rr, ii = rect_mul(
            ((f["re_lo"], f["re_hi"]), (f["im_lo"], f["im_hi"])),
            (((Fraction(0), exact(mp.exp, Fraction(-30) /
              (1 - (x0 / f["radius"]) ** 2))) if alive else (Fraction(0), Fraction(0))),
             (Fraction(0), Fraction(0))))
        phase = None
        if alive or True:
            mm = f["mod"]
            c_mid = exact(mp.cos, mm * ((x0 + x1) / 2))
            s_mid = exact(mp.sin, mm * ((x0 + x1) / 2))
            rho = abs(mm) * (x1 - x0) / 2
            phase = ((c_mid - rho, c_mid + rho), (s_mid - rho, s_mid + rho))
            rr, ii = rect_mul((rr, ii), phase)
        m_nonneg = f["mod"] >= 0
        for s in range(SAMPLES):
            xs = x0 + (x1 - x0) * Fraction(s, SAMPLES - 1)
            re_t, im_t = truth_value(f, xs)
            ok = rr[0] <= re_t <= rr[1] and ii[0] <= im_t <= ii[1]
            checks.append(ok)
            sum_re = iadd(sum_re, rr)
            sum_im = iadd(sum_im, ii)
        # sum-truth containment at samples too
        fam_out.append({
            "index": k, "alive": alive, "m_nonneg": m_nonneg,
            "radius_display": f"{float(f['radius']):.6e}",
            "re_box_display": [f"{float(v):.6e}" for v in rr],
            "im_box_display": [f"{float(v):.6e}" for v in ii],
        })
    # sum truth check
    sum_checks = []
    for s in range(SAMPLES):
        xs = x0 + (x1 - x0) * Fraction(s, SAMPLES - 1)
        re_t = im_t = Fraction(0)
        for f in fams:
            re_f, im_f = truth_value(f, xs)
            re_t += re_f
            im_t += im_f
        sum_checks.append(sum_re[0] <= re_t <= sum_re[1]
                          and sum_im[0] <= im_t <= sum_im[1])
    all_ok = all(checks) and all(sum_checks)
    # ---- emit Lean ----
    parts = [PREAMBLE]
    parts.append(f"def X0_2460 : ℝ := {r_lit(x0)}\n\n")
    parts.append(f"def X1_2460 : ℝ := {r_lit(x1)}\n\n")
    for k, f in enumerate(fams):
        parts.append(f"def mod{k}_2460 : ℝ := {r_lit(f['mod'])}\n\n")
        parts.append(f"def rad{k}_2460 : ℝ := {r_lit(f['radius'])}\n\n")
        parts.append(f"def coef{k}_2460 : ℂ := Complex.mk "
                     f"{r_lit(f['re_mid'])} {r_lit(f['im_mid'])}\n\n")
    for k, f in enumerate(fams):
        parts.append(fam_defs(k, f, f["radius"] > x0,
                              f["mod"] >= 0) + "\n")
    for k, f in enumerate(fams):
        parts.append(fam_lemma(k, f, f["radius"] > x0,
                               f["mod"] >= 0) + "\n")

    # rects2460 arms reference the same box defs as famPanelK statements
    def rect_expr(k):
        return (f"(ComplexRect2427.mul (ComplexRect2427.mul "
                f"coefRect{k}_2460 bumpBox{k}_2460) phaseBox{k}_2460)")

    rbody = "\n".join(f"  | {k} => {rect_expr(k)}" for k in range(FAMILIES))
    cbody = "\n".join(
        f"  | {k} => Complex.mk {r_lit(fams[k]['re_mid'])} "
        f"{r_lit(fams[k]['im_mid'])}" for k in range(FAMILIES))
    mbody = "\n".join(f"  | {k} => mod{k}_2460" for k in range(FAMILIES))
    radbody = "\n".join(f"  | {k} => rad{k}_2460" for k in range(FAMILIES))
    parts.append(f"""noncomputable def rects2460 (i : Fin {FAMILIES}) : ComplexRect2427 :=
  match i.val with
{rbody}
  | _ => {{ reLo := 0, reHi := 0, imLo := 0, imHi := 0 }}

def coefs2460 (i : Fin {FAMILIES}) : ℂ :=
  match i.val with
{cbody}
  | _ => 0

def mods2460 (i : Fin {FAMILIES}) : ℝ :=
  match i.val with
{mbody}
  | _ => 0

def rads2460 (i : Fin {FAMILIES}) : ℝ :=
  match i.val with
{radbody}
  | _ => 0

theorem sumPanelSample_2460 (x : ℝ) (hx : x ∈ Set.Icc X0_2460 X1_2460) :
    (ComplexRect2427.sumFinset rects2460 Finset.univ).Mem
      (∑ i : Fin {FAMILIES},
        externalFamilyValue2344 (coefs2460 i) (mods2460 i) (rads2460 i) x) := by
  refine sumPanelMem_2459 rects2460 (fun i x hx => ?_) x hx
  fin_cases i
  exacts [{", ".join(f"famPanel{k}_2460 x hx" for k in range(FAMILIES))}]

end ConnesWeilRH.Dev
""")
    OUT_LEAN.write_text("".join(parts), encoding="utf-8")
    out = {
        "record": 2460,
        "verdict": "OWNER-PANEL-SAMPLE-COMPLETE" if all_ok
        else "OWNER-PANEL-SAMPLE-CONTAINMENT-FAIL",
        "scope": "one-panel door instantiation with 2338 coefficient balls; "
                 "diagnostic sample, no trapezoid sum, no zeta, no strip "
                 "norm discharged, no GO, no RH claim",
        "panel_x0": str(x0), "panel_x1": str(x1),
        "panel_contains_quarter": True,
        "h_grid": str(h),
        "alive_families": sum(1 for f in fams if f["radius"] > x0),
        "dead_families": sum(1 for f in fams if f["radius"] <= x0),
        "family_containment_5x30": all(checks),
        "sum_containment_5": all(sum_checks),
        "families": fam_out,
        "sum_re_box_display": [f"{float(v):.6e}" for v in sum_re],
        "sum_im_box_display": [f"{float(v):.6e}" for v in sum_im],
        "lean_file": str(OUT_LEAN.relative_to(ROOT)).replace("\\\\", "/"),
        "lean_file_bytes": len(OUT_LEAN.read_bytes()),
        "producer_go": False,
        "rh_claim": False,
        **pins,
    }
    OUT_JSON.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "verdict": out["verdict"],
        "panel": [str(x0), str(x1)],
        "alive": out["alive_families"], "dead": out["dead_families"],
        "family_containment": out["family_containment_5x30"],
        "sum_containment": out["sum_containment_5"],
        "lean_lines": OUT_LEAN.read_text(encoding="utf-8").count("\n"),
    }, indent=2))


if __name__ == "__main__":
    main()
