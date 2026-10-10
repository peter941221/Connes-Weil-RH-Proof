"""Generate per-panel analytic containment modules for entry (0, 3) (record 2656).

Templatizes the record-2649 pilot (panel 109) over the full 190-panel cover:
each module consumes the per-panel record-2655 tables through the
record-2647 generic stability layer and proves

    ||integral exp(phase(u) - phase(0))||
      <= |integral P| + exp(2 * VAR) * (residualUpper / deficitLower^2) * 2h^2

with per-panel EXACT rationals
    center c, edge bound B = |c| + 1/200, deficitLower = 1 - B^2,
    drift factor F = 2|c| + 1/200, drift = F/200,
    deficit-part delta = 30 * drift / deficitLower^2,
    variation VAR = 1/25 + delta        (beta-part <= 8/200 = 1/25).

Panel 109 is skipped (its certificate is the committed record-2649 pilot).
Edge panels get true-but-vacuous bounds (delta explodes as the deficit
dips); the containment brick routes those through the monotone edge
argument, per the 2649 next-steps.

Scope: per-panel certificates only.  No off-diagonal claim, no entry
containment, no Producer GO, no SourceRH, no RH.
"""

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))

from offdiagonal_residual_pricing_2624 import ROW, column_parameters, panel_center

ROOT = Path(__file__).resolve().parents[1]
HALF = Fraction(1, 200)
RECORD = 2656
SKIP = {109}  # committed pilot, record 2649


def q(value):
    value = Fraction(value)
    if value.denominator == 1:
        return f"({value.numerator})"
    return f"({value.numerator} / {value.denominator})"


TEMPLATE = r"""import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P@@TAG@@

namespace ConnesWeilRH.Dev

open Set

-- The panel-local phase/derivative lines exceed the 100-character style
-- limit by construction.
set_option linter.style.longLine false

/-!
# Complex analytic containment of panel @@TAG@@ (record @@RECORD@@)

Per-panel instance of the record-2649 pilot template: the analytic layer
consuming the record-@@DPRE@@ data tables through the record-2647 generic
stability theorem.  The panel phase is

    phase(u) = (beta + i*psi) * u - 30 / (1 - (center + u)^2),

whose derivative `beta + i*psi - 60*(center + u)/D(u)` satisfies the exact
quotient identity behind the residual replay, so
`|P' - phase' * P| <= residualUpper / deficitLower^2` on the panel.  The
real part of the phase varies by at most @@VAR@@ on the panel, which turns
the record-2647 stability into the pointwise bound

    ||exp(phase(u) - phase(0)) - P(u)|| <= exp(2*VAR) * residualUpper/DLOW^2 * |u|,

integrated to the panel-local analytic containment certificate.  All
constants are exact rationals derived from the panel center @@CENTER@@.
Scope: this panel only.  No off-diagonal claim, no entry containment.
-/

def complexPanelHalfWidth@@R@@ : QQT := 1 / 200

def complexPanelHalfWidthReal@@R@@ : RR := (complexPanelHalfWidth@@R@@ : RR)

noncomputable def complexPanelDeficitValue@@R@@ (position : RR) : RR :=
  1 - ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position) ^ 2

noncomputable def complexPanelBetaComplex@@R@@ : CC :=
  ((complexPanelBeta@@DPRE@@P@@TAG@@ : RR) : CC) + ((complexPanelPsi@@DPRE@@P@@TAG@@ : RR) : CC) * Complex.I

noncomputable def complexPanelPhase@@R@@ (position : RR) : CC :=
  complexPanelBetaComplex@@R@@ * (position : CC)
    + Complex.ofReal ((-30 : RR) / complexPanelDeficitValue@@R@@ position)

noncomputable def complexPanelPhaseDerivative@@R@@ (position : RR) : CC :=
  complexPanelBetaComplex@@R@@
    + Complex.ofReal ((-60 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)
        / complexPanelDeficitValue@@R@@ position ^ 2)

theorem complexPanelHalfWidth_nonneg@@R@@ : 0 <= complexPanelHalfWidth@@R@@ := by
  norm_num [complexPanelHalfWidth@@R@@]

theorem complexPanelHalfWidthReal_nonneg@@R@@ : 0 <= complexPanelHalfWidthReal@@R@@ := by
  norm_num [complexPanelHalfWidthReal@@R@@, complexPanelHalfWidth@@R@@]

theorem complexPanelBeta_abs_le@@R@@ : |complexPanelBeta@@DPRE@@P@@TAG@@| <= 8 := by
  decide +kernel

theorem complexPanelAbsInside@@R@@ (position : RR) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :
    |position| <= (1 / 200 : RR) := by
  have h := abs_le.mpr ⟨hinside.1, hinside.2⟩
  push_cast at h
  exact h.trans (by norm_num [complexPanelHalfWidthReal@@R@@, complexPanelHalfWidth@@R@@])

theorem complexPanelDeficit_lower@@R@@ (position : RR) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :
    ((@@DLOW@@ : RR)) <= complexPanelDeficitValue@@R@@ position := by
  have hcenter : ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR)) = (@@CENTER@@ : RR) := by
    norm_num [complexPanelCenter@@DPRE@@P@@TAG@@]
  have habspos : |position| <= (1 / 200 : RR) := complexPanelAbsInside@@R@@ position hinside
  have hcabs : |((complexPanelCenter@@DPRE@@P@@TAG@@ : RR)) + position| <= (@@B@@ : RR) := by
    rw [hcenter]
    calc |(@@CENTER@@ : RR) + position| <= |(@@CENTER@@ : RR)| + |position| := abs_add_le _ _
      _ <= (@@B@@ : RR) := by
            rw [@@ABSSIGN@@]
            linarith
  obtain ⟨q1, q2⟩ := abs_le.mp hcabs
  have hsq : ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position) ^ 2 <= (@@B@@ : RR) ^ 2 := by
    nlinarith
  dsimp only [complexPanelDeficitValue@@R@@]
  linarith

theorem complexPanelDeficit_eval@@R@@ (position : RR) :
    complexPolyEval2647 complexPanelDeficit@@DPRE@@P@@TAG@@ position
      = ((complexPanelDeficitValue@@R@@ position : RR) : CC) := by
  apply Complex.ext
  · simp only [complexPolyEval2647, complexPanelDeficit@@DPRE@@P@@TAG@@, embedPair2542,
      complexPanelDeficitValue@@R@@, complexPanelCenter@@DPRE@@P@@TAG@@, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im]
    push_cast
    ring
  · simp only [complexPolyEval2647, complexPanelDeficit@@DPRE@@P@@TAG@@, embedPair2542,
      complexPanelDeficitValue@@R@@, complexPanelCenter@@DPRE@@P@@TAG@@, Complex.add_im,
      Complex.mul_im, Complex.ofReal_im, Complex.zero_im]
    ring

theorem complexPanelNumerator_eval@@R@@ (position : RR) :
    complexPolyEval2647 complexPanelNumerator@@DPRE@@P@@TAG@@ position
      = complexPanelBetaComplex@@R@@
          * (((complexPanelDeficitValue@@R@@ position : RR) : CC) ^ 2)
        - Complex.ofReal ((60 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)) := by
  apply Complex.ext
  · simp only [complexPolyEval2647, complexPanelNumerator@@DPRE@@P@@TAG@@, embedPair2542,
      complexPanelDeficitValue@@R@@, complexPanelBetaComplex@@R@@,
      complexPanelCenter@@DPRE@@P@@TAG@@, complexPanelBeta@@DPRE@@P@@TAG@@, complexPanelPsi@@DPRE@@P@@TAG@@,
      pow_two, Complex.sub_re, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im]
    push_cast
    ring
  · simp only [complexPolyEval2647, complexPanelNumerator@@DPRE@@P@@TAG@@, embedPair2542,
      complexPanelDeficitValue@@R@@, complexPanelBetaComplex@@R@@,
      complexPanelCenter@@DPRE@@P@@TAG@@, complexPanelBeta@@DPRE@@P@@TAG@@, complexPanelPsi@@DPRE@@P@@TAG@@,
      pow_two, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im]
    push_cast
    ring

theorem complexPanelPhaseReal_hasDerivAt@@R@@ (position : RR)
    (hdeficit : complexPanelDeficitValue@@R@@ position ≠ 0) :
    HasDerivAt (fun x : RR => (-30 : RR) / complexPanelDeficitValue@@R@@ x)
      (((-60 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)
        / complexPanelDeficitValue@@R@@ position ^ 2)) position := by
  have hinner : HasDerivAt (fun x : RR => ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + x))
      (1 : RR) position := by
    simpa using (hasDerivAt_const position (complexPanelCenter@@DPRE@@P@@TAG@@ : RR)).add
      (hasDerivAt_id position)
  have hdenominator : HasDerivAt
      (fun x : RR => (1 : RR) - ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + x) ^ 2)
      ((-2 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)) position := by
    simpa using (hasDerivAt_const position (1 : RR)).sub (hinner.pow 2)
  have hquotient : HasDerivAt
      (fun x : RR => (-30 : RR) / complexPanelDeficitValue@@R@@ x)
      (((-30 : RR) * -(-2 * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position))) /
        complexPanelDeficitValue@@R@@ position ^ 2) position := by
    simpa using (hasDerivAt_const position (-30 : RR)).div hdenominator hdeficit
  convert hquotient using 1
  ring

theorem complexPanelPhase_hasDerivAt@@R@@ (position : RR)
    (hdeficit : complexPanelDeficitValue@@R@@ position ≠ 0) :
    HasDerivAt complexPanelPhase@@R@@ (complexPanelPhaseDerivative@@R@@ position) position := by
  have hreal := complexPanelPhaseReal_hasDerivAt@@R@@ position hdeficit
  have hrealC := hreal.ofReal_comp
  have hid : HasDerivAt (fun y : RR => ((y : RR) : CC)) 1 position :=
    (hasDerivAt_id position).ofReal_comp
  have hlin : HasDerivAt (fun y : RR => complexPanelBetaComplex@@R@@ * ((y : RR) : CC))
      (complexPanelBetaComplex@@R@@ * 1) position := HasDerivAt.const_mul _ hid
  have hsum := hlin.add hrealC
  convert hsum using 1
  · dsimp only [complexPanelPhaseDerivative@@R@@]
    ring

set_option maxHeartbeats 2000000 in
-- the 57-slot zero-scaled rational fold needs the 2621 heartbeat ceiling
theorem complexPanelPolynomial_zero@@R@@ :
    complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ 0 = 1 := by
  rw [← Rat.cast_zero (α := RR), complexPolyEval2647_cast]
  have hzero : complexPolyEvalRat2647 0 complexPanelPolynomial@@DPRE@@P@@TAG@@ = (1, 0) := by
    decide +kernel
  rw [hzero, embedPair_one2542]

theorem complexPanelStabilityResidual@@R@@ (position : RR) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :
    ‖complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial@@DPRE@@P@@TAG@@) position
        - complexPanelPhaseDerivative@@R@@ position
            * complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position‖
      <= ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR) := by
  have hlower := complexPanelDeficit_lower@@R@@ position hinside
  have habs := complexPanelAbsInside@@R@@ position hinside
  have hpos : (0 : RR) < complexPanelDeficitValue@@R@@ position := by linarith
  have hneC : (((complexPanelDeficitValue@@R@@ position : RR) : CC)) ^ 2 ≠ 0 := by
    have hd : ((complexPanelDeficitValue@@R@@ position : RR) : CC) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]
      exact ne_of_gt hpos
    exact pow_ne_zero 2 hd
  have hom := congrArg (fun L => complexPolyEval2647 L position)
    complexPanelResidual_replay@@DPRE@@P@@TAG@@
  simp only [complexPolyEval2647_add, complexPolyEval2647_mul, complexPolyEval2647_scale,
    complexPanelDeficit_eval@@R@@] at hom
  have hneg1 : embedPair2542 (-1, 0) = (-1 : CC) := by
    apply Complex.ext <;> simp [embedPair2542]
  rw [hneg1, complexPanelNumerator_eval@@R@@] at hom
  push_cast at hom
  have hcanc : Complex.ofReal ((-60 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)
        / complexPanelDeficitValue@@R@@ position ^ 2)
      * (((complexPanelDeficitValue@@R@@ position : RR) : CC) ^ 2)
      = Complex.ofReal ((-60 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hrel : complexPanelPhaseDerivative@@R@@ position
        * (((complexPanelDeficitValue@@R@@ position : RR) : CC) ^ 2)
      = complexPanelBetaComplex@@R@@
          * (((complexPanelDeficitValue@@R@@ position : RR) : CC) ^ 2)
        - Complex.ofReal ((60 : RR) * ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR) + position)) := by
    dsimp only [complexPanelPhaseDerivative@@R@@]
    rw [add_mul, hcanc]
    push_cast
    ring
  push_cast at hrel
  have hkey : (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial@@DPRE@@P@@TAG@@) position
        - complexPanelPhaseDerivative@@R@@ position
            * complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)
        * (((complexPanelDeficitValue@@R@@ position : RR) : CC) ^ 2)
      = complexPolyEval2647 complexPanelResidual@@DPRE@@P@@TAG@@ position := by
    rw [← pow_two] at hom
    rw [sub_mul, mul_right_comm, hrel]
    rw [← hom]
    ring
  have hsplit : complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial@@DPRE@@P@@TAG@@) position
        - complexPanelPhaseDerivative@@R@@ position
            * complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position
      = complexPolyEval2647 complexPanelResidual@@DPRE@@P@@TAG@@ position
          / (((complexPanelDeficitValue@@R@@ position : RR) : CC) ^ 2) := by
    rw [eq_div_iff hneC]
    exact hkey
  have habsQ : |position| <= ((complexPanelHalfWidth@@R@@ : QQT) : RR) := by
    norm_num [complexPanelHalfWidth@@R@@]
    exact habs
  rw [hsplit, norm_div]
  have habsBound : ‖complexPolyEval2647 complexPanelResidual@@DPRE@@P@@TAG@@ position‖
      <= ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ : QQT) : RR) := by
    rw [← complexPanelResidualUpper_replay@@DPRE@@P@@TAG@@]
    exact complexPolyEval2647_abs_le complexPanelResidual@@DPRE@@P@@TAG@@
      complexPanelHalfWidth@@R@@ complexPanelHalfWidth_nonneg@@R@@ position habsQ
  have hRUpos : (0 : RR) < ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ : QQT) : RR) :=
    Rat.cast_pos.mpr (by norm_num [complexPanelResidualUpper@@DPRE@@P@@TAG@@])
  calc ‖complexPolyEval2647 complexPanelResidual@@DPRE@@P@@TAG@@ position‖
        / ‖(((complexPanelDeficitValue@@R@@ position : RR)) : CC) ^ 2‖
      <= ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ : QQT) : RR)
          / complexPanelDeficitValue@@R@@ position ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        exact (div_le_div_iff_of_pos_right (pow_pos hpos 2)).mpr habsBound
    _ <= ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ : QQT) : RR)
          / ((@@DLOW@@ : RR)) ^ 2 := by
        exact (div_le_div_iff_of_pos_left hRUpos (pow_pos hpos 2)
          (pow_pos (by norm_num : (0 : RR) < (@@DLOW@@ : RR)) 2)).mpr
          (pow_le_pow_left₀ (by norm_num) hlower 2)
    _ = ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR) := by
        norm_num [complexPanelResidualUpper@@DPRE@@P@@TAG@@]

/-! ## Real-part variation of the panel phase -/

theorem complexPanelReVariation@@R@@ (position : RR) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :
    |(complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0).re| <= (@@VAR@@ : RR) := by
  have hcastC : ((complexPanelCenter@@DPRE@@P@@TAG@@ : RR)) = (@@CENTER@@ : RR) := by
    norm_num [complexPanelCenter@@DPRE@@P@@TAG@@]
  have habs : |position| <= (1 / 200 : RR) := complexPanelAbsInside@@R@@ position hinside
  have hlower := complexPanelDeficit_lower@@R@@ position hinside
  have hpos : (0 : RR) < complexPanelDeficitValue@@R@@ position := by linarith
  have hapos : (0 : RR) < 1 - (@@CENTER@@ : RR) ^ 2 := by norm_num
  -- |30 * (1/a - 1/d)| <= delta with a = 1 - c^2, d = 1 - (c + position)^2;
  -- the numerator identity is 30*(d - a)/(a*d), NOT 30*(a - d)/(a*d)
  have hR : |(-30 : RR) / complexPanelDeficitValue@@R@@ position
      + 30 / (1 - (@@CENTER@@ : RR) ^ 2)| <= (@@DELTA@@ : RR) := by
    have hexpr : (-30 : RR) / complexPanelDeficitValue@@R@@ position
        + 30 / (1 - (@@CENTER@@ : RR) ^ 2)
        = 30 * (complexPanelDeficitValue@@R@@ position - (1 - (@@CENTER@@ : RR) ^ 2))
          / ((1 - (@@CENTER@@ : RR) ^ 2) * complexPanelDeficitValue@@R@@ position) := by
      field_simp
      ring
    have hdelta : complexPanelDeficitValue@@R@@ position - (1 - (@@CENTER@@ : RR) ^ 2)
        = -((2 * (@@CENTER@@ : RR) + position) * position) := by
      dsimp only [complexPanelDeficitValue@@R@@]
      rw [hcastC]
      ring
    have hprod : (0 : RR) < (1 - (@@CENTER@@ : RR) ^ 2)
        * complexPanelDeficitValue@@R@@ position := mul_pos hapos hpos
    have hnum : |(2 * (@@CENTER@@ : RR) + position) * position|
        <= ((@@FACTOR@@ : RR)) * (1 / 200 : RR) := by
      rw [abs_mul]
      have h1 : |2 * (@@CENTER@@ : RR) + position| <= ((@@FACTOR@@ : RR)) := by
        calc |2 * (@@CENTER@@ : RR) + position|
            <= |2 * (@@CENTER@@ : RR)| + |position| := abs_add_le _ _
          _ <= ((@@TWOABS@@ : RR)) + (1 / 200 : RR) := by
                rw [@@BETASIGN@@]
                linarith
          _ = ((@@FACTOR@@ : RR)) := by norm_num
      calc |2 * (@@CENTER@@ : RR) + position| * |position|
          <= ((@@FACTOR@@ : RR)) * |position| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg position)
        _ <= ((@@FACTOR@@ : RR)) * (1 / 200 : RR) :=
            mul_le_mul_of_nonneg_left habs (by norm_num : (0 : RR) <= (@@FACTOR@@ : RR))
    have hconst : (30 : RR) * ((@@FACTOR@@ : RR) * (1 / 200 : RR))
        <= (@@DELTA@@ : RR) * ((1 - (@@CENTER@@ : RR) ^ 2) * (@@DLOW@@ : RR)) := by norm_num
    rw [hexpr, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : RR) < 30),
      abs_of_pos hprod, hdelta, abs_neg, div_le_iff₀ hprod]
    refine le_trans (mul_le_mul_of_nonneg_left hnum (by norm_num)) ?_
    refine le_trans hconst ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlower
      (by norm_num : (0 : RR) <= 1 - (@@CENTER@@ : RR) ^ 2))
      (by norm_num : (0 : RR) <= (@@DELTA@@ : RR))
  -- |beta * position| <= 1/25
  have hbeta8 : |((complexPanelBeta@@DPRE@@P@@TAG@@ : RR))| <= (8 : RR) := by
    exact_mod_cast complexPanelBeta_abs_le@@R@@
  have hbeta : |((complexPanelBeta@@DPRE@@P@@TAG@@ : RR)) * position| <= (1 / 25 : RR) := by
    calc |((complexPanelBeta@@DPRE@@P@@TAG@@ : RR)) * position|
        = |((complexPanelBeta@@DPRE@@P@@TAG@@ : RR))| * |position| := abs_mul _ _
      _ <= (8 : RR) * |position| :=
          mul_le_mul_of_nonneg_right hbeta8 (abs_nonneg position)
      _ <= (8 : RR) * (1 / 200 : RR) :=
          mul_le_mul_of_nonneg_left habs (by norm_num : (0 : RR) <= 8)
      _ <= (1 / 25 : RR) := by norm_num
  have htermPos : (complexPanelBetaComplex@@R@@ * ((position : RR) : CC)).re
      = ((complexPanelBeta@@DPRE@@P@@TAG@@ : RR)) * position := by
    dsimp only [complexPanelBetaComplex@@R@@]
    simp [Complex.mul_re]
  have hterm0 : (complexPanelBetaComplex@@R@@ * ((0 : RR) : CC)).re = 0 := by
    dsimp only [complexPanelBetaComplex@@R@@]
    simp
  have hsplit : (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0).re
      = (complexPanelBetaComplex@@R@@ * ((position : RR) : CC)).re
        + (Complex.ofReal ((-30 : RR) / complexPanelDeficitValue@@R@@ position)).re
        - (Complex.ofReal ((-30 : RR) / complexPanelDeficitValue@@R@@ 0)).re := by
    dsimp only [complexPanelPhase@@R@@]
    simp only [Complex.sub_re, Complex.add_re, hterm0, zero_add]
  have hofRe : ∀ x : RR, (Complex.ofReal x).re = x := fun x => by simp
  have hdef0 : complexPanelDeficitValue@@R@@ 0 = 1 - (@@CENTER@@ : RR) ^ 2 := by
    dsimp only [complexPanelDeficitValue@@R@@]
    rw [hcastC]
    ring
  rw [hsplit, htermPos, hofRe, hofRe, hdef0]
  have hfold : ((complexPanelBeta@@DPRE@@P@@TAG@@ : RR)) * position
        + (-30 : RR) / complexPanelDeficitValue@@R@@ position
        - (-30 : RR) / (1 - (@@CENTER@@ : RR) ^ 2)
      = ((complexPanelBeta@@DPRE@@P@@TAG@@ : RR)) * position
        + ((-30 : RR) / complexPanelDeficitValue@@R@@ position
          + 30 / (1 - (@@CENTER@@ : RR) ^ 2)) := by
    ring
  rw [hfold]
  calc _ <= |((complexPanelBeta@@DPRE@@P@@TAG@@ : RR)) * position|
        + |(-30 : RR) / complexPanelDeficitValue@@R@@ position
          + 30 / (1 - (@@CENTER@@ : RR) ^ 2)| := abs_add_le _ _
    _ <= (1 / 25 : RR) + (@@DELTA@@ : RR) := add_le_add hbeta hR
    _ <= (@@VAR@@ : RR) := by norm_num

/-! ## The generic complex integral error lemma -/

theorem complexExpPolynomialIntegralError@@R@@
    (phase phaseDerivative polynomial polynomialDerivative : RR → CC)
    (halfWidth variation residualUpper : RR) (hwidth : 0 <= halfWidth)
    (hpolynomialZero : polynomial 0 = 1)
    (hphaseDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt phase (phaseDerivative position) position)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hreVariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |(phase position - phase 0).re| <= variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      ‖polynomialDerivative position - phaseDerivative position * polynomial position‖
        <= residualUpper) :
    ‖(∫ position in (-halfWidth)..halfWidth,
        Complex.exp (phase position - phase 0) - polynomial position)‖
      <= Real.exp (2 * variation) * residualUpper * (2 * halfWidth ^ 2) := by
  have horder : -halfWidth <= halfWidth := by linarith
  have hzero : (0 : RR) ∈ Icc (-halfWidth) halfWidth := ⟨by linarith, hwidth⟩
  have hRU : (0 : RR) <= residualUpper := (norm_nonneg _).trans (hresidual 0 hzero)
  have hpointwise : ∀ position ∈ Set.uIoc (-halfWidth) halfWidth,
      ‖Complex.exp (phase position - phase 0) - polynomial position‖
        <= Real.exp (2 * variation) * residualUpper * halfWidth := by
    intro position hposition
    rw [Set.uIoc_of_le horder] at hposition
    obtain ⟨hpos1, hpos2⟩ := hposition
    have hclosed : position ∈ Icc (-halfWidth) halfWidth :=
      ⟨le_of_lt hpos1, hpos2⟩
    have habs : |position| <= halfWidth := abs_le.mpr ⟨le_of_lt hpos1, hpos2⟩
    have hstable := complexExpPolynomialResidualStability2647 phase phaseDerivative
      polynomial polynomialDerivative halfWidth variation residualUpper hwidth
      hpolynomialZero hphaseDerivative hpolynomialDerivative hreVariation hresidual
      position hclosed
    exact hstable.trans (mul_le_mul_of_nonneg_left habs
      (mul_nonneg (Real.exp_nonneg _) hRU))
  have hphaseCont : ContinuousOn (fun coordinate => Complex.exp (phase coordinate - phase 0))
      (Icc (-halfWidth) halfWidth) := by
    intro coordinate hcoordinate
    have hsub := (hphaseDerivative coordinate hcoordinate).sub
      (hasDerivAt_const coordinate (phase 0))
    have hsub' : HasDerivAt (fun x => phase x - phase 0)
        (phaseDerivative coordinate) coordinate := by
      convert hsub using 1
      ring
    refine ((Complex.hasDerivAt_exp (phase coordinate - phase 0)).comp
      coordinate hsub').continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn polynomial (Icc (-halfWidth) halfWidth) :=
    HasDerivAt.continuousOn fun coordinate hcoordinate =>
      hpolynomialDerivative coordinate hcoordinate
  have hint : IntervalIntegrable
      (fun coordinate => Complex.exp (phase coordinate - phase 0) - polynomial coordinate)
      MeasureTheory.volume (-halfWidth) halfWidth :=
    (hphaseCont.sub hpolyCont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpointwise
  rw [abs_of_nonneg (by linarith : (0 : RR) <= halfWidth - -halfWidth)] at hbound
  calc ‖(∫ position in (-halfWidth)..halfWidth,
        Complex.exp (phase position - phase 0) - polynomial position)‖
      <= Real.exp (2 * variation) * residualUpper * halfWidth
          * (halfWidth - -halfWidth) := hbound
    _ = Real.exp (2 * variation) * residualUpper * (2 * halfWidth ^ 2) := by ring

/-! ## The panel instance and the certificate -/

theorem complexPanelPointwise@@R@@ (position : RR) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :
    ‖Complex.exp (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0)
        - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position‖
      <= Real.exp (2 * (@@VAR@@ : RR))
          * ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
          * |position| := by
  have hphaseDeriv : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal@@R@@)
      complexPanelHalfWidthReal@@R@@,
      HasDerivAt complexPanelPhase@@R@@
        (complexPanelPhaseDerivative@@R@@ coordinate) coordinate := by
    intro coordinate hcoordinate
    refine complexPanelPhase_hasDerivAt@@R@@ coordinate ?_
    have hlower := complexPanelDeficit_lower@@R@@ coordinate hcoordinate
    linarith
  have hresid : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal@@R@@)
      complexPanelHalfWidthReal@@R@@,
      ‖complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial@@DPRE@@P@@TAG@@) coordinate
          - complexPanelPhaseDerivative@@R@@ coordinate
              * complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate‖
        <= ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR) :=
    complexPanelStabilityResidual@@R@@
  have hkey := complexExpPolynomialResidualStability2647 complexPanelPhase@@R@@
    complexPanelPhaseDerivative@@R@@
    (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@)
    (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial@@DPRE@@P@@TAG@@))
    complexPanelHalfWidthReal@@R@@ (@@VAR@@ : RR)
    ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
    complexPanelHalfWidthReal_nonneg@@R@@
    complexPanelPolynomial_zero@@R@@ hphaseDeriv
    (fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate)
    complexPanelReVariation@@R@@ hresid position hinside
  norm_num at hkey ⊢
  exact hkey

theorem complexPanelIntegralError@@R@@ :
    ‖(∫ position in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
        Complex.exp (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0)
          - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)‖
      <= Real.exp (2 * (@@VAR@@ : RR))
          * ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
          * (2 * complexPanelHalfWidthReal@@R@@ ^ 2) := by
  have hphaseDeriv : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal@@R@@)
      complexPanelHalfWidthReal@@R@@,
      HasDerivAt complexPanelPhase@@R@@
        (complexPanelPhaseDerivative@@R@@ coordinate) coordinate := by
    intro coordinate hcoordinate
    refine complexPanelPhase_hasDerivAt@@R@@ coordinate ?_
    have hlower := complexPanelDeficit_lower@@R@@ coordinate hcoordinate
    linarith
  have hresid := complexPanelStabilityResidual@@R@@
  have hkey := complexExpPolynomialIntegralError@@R@@ complexPanelPhase@@R@@
    complexPanelPhaseDerivative@@R@@
    (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@)
    (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial@@DPRE@@P@@TAG@@))
    complexPanelHalfWidthReal@@R@@ (@@VAR@@ : RR)
    ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
    complexPanelHalfWidthReal_nonneg@@R@@
    complexPanelPolynomial_zero@@R@@ hphaseDeriv
    (fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate)
    complexPanelReVariation@@R@@ hresid
  norm_num at hkey ⊢
  exact hkey

theorem complexPanelPolyIntegral@@R@@ :
    (∫ position in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
      complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)
      = embedPair2542 complexPanelIntegral@@DPRE@@P@@TAG@@ := by
  have horder : -complexPanelHalfWidthReal@@R@@ <= complexPanelHalfWidthReal@@R@@ := by
    norm_num [complexPanelHalfWidthReal@@R@@, complexPanelHalfWidth@@R@@]
  have hanti : ∀ coordinate ∈ Set.uIcc (-complexPanelHalfWidthReal@@R@@)
      complexPanelHalfWidthReal@@R@@,
      HasDerivAt (complexPolyEval2647 complexPanelPrimitive@@DPRE@@P@@TAG@@)
        (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate) coordinate := by
    intro coordinate _
    have h := complexPolyEval2647_hasDerivAt complexPanelPrimitive@@DPRE@@P@@TAG@@ coordinate
    rwa [complexPanelPrimitive_replay@@DPRE@@P@@TAG@@] at h
  have hpolyCont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@)
      (Icc (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :=
    HasDerivAt.continuousOn fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate
  have hint : IntervalIntegrable
      (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@) MeasureTheory.volume
      (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@ :=
    hpolyCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hanti hint
  have hcastPos : complexPolyEval2647 complexPanelPrimitive@@DPRE@@P@@TAG@@
      complexPanelHalfWidthReal@@R@@
      = embedPair2542 (complexPolyEvalRat2647 complexPanelHalfWidth@@R@@
        complexPanelPrimitive@@DPRE@@P@@TAG@@) := complexPolyEval2647_cast _ _
  have hcastNeg : complexPolyEval2647 complexPanelPrimitive@@DPRE@@P@@TAG@@
      (-complexPanelHalfWidthReal@@R@@)
      = embedPair2542 (complexPolyEvalRat2647 (-complexPanelHalfWidth@@R@@)
        complexPanelPrimitive@@DPRE@@P@@TAG@@) := by
    have h2 := complexPolyEval2647_cast complexPanelPrimitive@@DPRE@@P@@TAG@@
      (-complexPanelHalfWidth@@R@@)
    rwa [Rat.cast_neg] at h2
  rw [hsub, hcastPos, hcastNeg]
  apply Complex.ext
  · simp only [embedPair2542, Complex.sub_re]
    norm_num [complexPanelHalfWidth@@R@@]
    exact_mod_cast complexPanelIntegral_re@@DPRE@@P@@TAG@@
  · simp only [embedPair2542, Complex.sub_im]
    norm_num [complexPanelHalfWidth@@R@@]
    exact_mod_cast complexPanelIntegral_im@@DPRE@@P@@TAG@@

theorem complexPanelAnalyticCertificate@@R@@ :
    ‖(∫ position in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
        Complex.exp (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0))‖
      <= ((pairMagnitude2542 complexPanelIntegral@@DPRE@@P@@TAG@@ : QQT) : RR)
        + Real.exp (2 * (@@VAR@@ : RR))
            * ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
            * (2 * complexPanelHalfWidthReal@@R@@ ^ 2) := by
  have horder : -complexPanelHalfWidthReal@@R@@ <= complexPanelHalfWidthReal@@R@@ := by
    norm_num [complexPanelHalfWidthReal@@R@@, complexPanelHalfWidth@@R@@]
  have hphaseCont : ContinuousOn (fun coordinate =>
      Complex.exp (complexPanelPhase@@R@@ coordinate - complexPanelPhase@@R@@ 0))
      (Icc (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) := by
    intro coordinate hcoordinate
    have hd : complexPanelDeficitValue@@R@@ coordinate ≠ 0 := by
      have hlower := complexPanelDeficit_lower@@R@@ coordinate hcoordinate
      linarith
    have hsub := (complexPanelPhase_hasDerivAt@@R@@ coordinate hd).sub
      (hasDerivAt_const coordinate (complexPanelPhase@@R@@ 0))
    have hsub' : HasDerivAt (fun x => complexPanelPhase@@R@@ x - complexPanelPhase@@R@@ 0)
        (complexPanelPhaseDerivative@@R@@ coordinate) coordinate := by
      convert hsub using 1
      ring
    refine ((Complex.hasDerivAt_exp (complexPanelPhase@@R@@ coordinate
      - complexPanelPhase@@R@@ 0)).comp coordinate hsub').continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@)
      (Icc (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@) :=
    HasDerivAt.continuousOn fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate
  have hexpInt : IntervalIntegrable (fun coordinate =>
      Complex.exp (complexPanelPhase@@R@@ coordinate - complexPanelPhase@@R@@ 0))
      MeasureTheory.volume (-complexPanelHalfWidthReal@@R@@)
      complexPanelHalfWidthReal@@R@@ :=
    hphaseCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hpolyInt : IntervalIntegrable
      (complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@) MeasureTheory.volume
      (-complexPanelHalfWidthReal@@R@@) complexPanelHalfWidthReal@@R@@ :=
    hpolyCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hsubInt : IntervalIntegrable (fun coordinate =>
      Complex.exp (complexPanelPhase@@R@@ coordinate - complexPanelPhase@@R@@ 0)
        - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate)
      MeasureTheory.volume (-complexPanelHalfWidthReal@@R@@)
      complexPanelHalfWidthReal@@R@@ := hexpInt.sub hpolyInt
  have herror := complexPanelIntegralError@@R@@
  have hfun : (fun coordinate => Complex.exp (complexPanelPhase@@R@@ coordinate
          - complexPanelPhase@@R@@ 0))
      = fun coordinate => (Complex.exp (complexPanelPhase@@R@@ coordinate
            - complexPanelPhase@@R@@ 0)
          - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate)
        + complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate := by
    funext coordinate
    ring
  rw [hfun]
  have hintsplit : (∫ position in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
        (Complex.exp (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0)
          - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)
        + complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)
      = (∫ coordinate in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
          Complex.exp (complexPanelPhase@@R@@ coordinate - complexPanelPhase@@R@@ 0)
            - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate)
        + (∫ coordinate in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
            complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ coordinate) :=
    intervalIntegral.integral_add hsubInt hpolyInt
  rw [hintsplit, complexPanelPolyIntegral@@R@@]
  calc ‖(∫ position in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
          Complex.exp (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0)
            - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)
        + embedPair2542 complexPanelIntegral@@DPRE@@P@@TAG@@‖
      <= ‖(∫ position in (-complexPanelHalfWidthReal@@R@@)..complexPanelHalfWidthReal@@R@@,
            Complex.exp (complexPanelPhase@@R@@ position - complexPanelPhase@@R@@ 0)
              - complexPolyEval2647 complexPanelPolynomial@@DPRE@@P@@TAG@@ position)‖
        + ‖embedPair2542 complexPanelIntegral@@DPRE@@P@@TAG@@‖ := norm_add_le _ _
    _ <= Real.exp (2 * (@@VAR@@ : RR))
          * ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
          * (2 * complexPanelHalfWidthReal@@R@@ ^ 2)
        + (pairMagnitude2542 complexPanelIntegral@@DPRE@@P@@TAG@@ : RR) :=
          add_le_add herror (embedPair_magnitude2542 _)
    _ = ((pairMagnitude2542 complexPanelIntegral@@DPRE@@P@@TAG@@ : QQT) : RR)
        + Real.exp (2 * (@@VAR@@ : RR))
            * ((complexPanelResidualUpper@@DPRE@@P@@TAG@@ / ((@@DLOW@@ : QQT) ^ 2) : QQT) : RR)
            * (2 * complexPanelHalfWidthReal@@R@@ ^ 2) := by ring

end ConnesWeilRH.Dev
"""


def main():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    pilot = column_parameters(capture, 3)
    beta, psi = pilot["beta"], pilot["psi"]
    emitted = []
    for index in range(190):
        if index in SKIP:
            continue
        center = panel_center(index)
        tag = f"{index:03d}"
        trec = 2655
        b = abs(center) + HALF
        dlow = 1 - b * b
        factor = 2 * abs(center) + HALF
        delta = 30 * factor * HALF / (dlow * dlow)
        var = Fraction(1, 25) + delta
        twoabs = 2 * abs(center)
        if center > 0:
            abssign = f"abs_of_pos (by norm_num : (0 : ℝ) < ({q(center)} : ℝ))"
            betasign = f"abs_of_pos (by norm_num : (0 : ℝ) < 2 * ({q(center)} : ℝ))"
        else:
            abssign = f"abs_of_neg (by norm_num : ({q(center)} : ℝ) < 0)"
            betasign = f"abs_of_neg (by norm_num : 2 * ({q(center)} : ℝ) < 0)"
        body = TEMPLATE
        for key, value in {
            "@@TAG@@": tag, "@@DPRE@@": str(trec), "@@RECORD@@": str(RECORD),
            "@@R@@": f"{RECORD}P{tag}",
            "@@CENTER@@": q(center), "@@B@@": q(b), "@@DLOW@@": q(dlow),
            "@@FACTOR@@": q(factor), "@@TWOABS@@": q(twoabs),
            "@@DELTA@@": q(delta), "@@VAR@@": q(var),
            "@@DPRE@@": "2648", "@@ABSSIGN@@": abssign, "@@BETASIGN@@": betasign,
        }.items():
            body = body.replace(key, value)
        # bare-word type tokens (and the QQQ emitted by q()) -> real types
        import re
        body = re.sub(r"\bQQQ\b|\bQQT\b", "ℚ", body)
        body = re.sub(r"\bRR\b", "ℝ", body)
        body = re.sub(r"\bCC\b", "ℂ", body)
        out = ROOT / f"ConnesWeilRH/Dev/C1RouteAComplexPanelAnalytic{RECORD}P{tag}.lean"
        out.write_text(body, encoding="utf-8", newline="\n")
        emitted.append(dict(
            panel=index, center=str(center), b=str(b), dlow=str(dlow),
            delta=str(delta), var=str(var),
            residual_upper=None, module=out.name))
    payload = dict(
        record=RECORD, entry=[ROW, 3], panel_count=190, emitted=len(emitted),
        pilot_panel=109, pilot_record=2649,
        constants=dict(half_width=str(HALF), beta_exact=str(beta),
                       psi_exact=str(psi), beta_abs_bound="8",
                       beta_term_bound=str(Fraction(1, 25))),
        variation_formula="VAR = 1/25 + 30*(2|c|+1/200)/200 / (1-B^2)^2, B = |c|+1/200",
        panels=emitted,
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / f"results/{RECORD}_panel_analytic.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {len(emitted)} analytic modules; "
          f"var range [{min(float(Fraction(e['var'])) for e in emitted):.4f}, "
          f"{max(float(Fraction(e['var'])) for e in emitted):.4f}]")


if __name__ == "__main__":
    main()
