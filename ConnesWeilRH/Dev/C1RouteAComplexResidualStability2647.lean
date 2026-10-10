import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619
import ConnesWeilRH.Dev.C1RouteACompactExp2542

namespace ConnesWeilRH.Dev

open Set

/-!
# Complex list helpers and complex residual stability (record 2624 GO-route brick 2)

The off-diagonal panels (pilot entry (0,3), record 2624) approximate
`exp(complex phase)` by a complex polynomial whose coefficients are
exact rational pairs. This module supplies the generic layer the
generated tables instantiate:

* complex polynomial list helpers over `List RatPair2542` with the
  embed-hom theorems (`embedPair2542` from the certified 2542 layer),
* the complex residual stability theorem, the complex analog of
  `exp_polynomial_residual_stability2619`: the exponential factor
  bounds pass through the REAL part of the phase (`Complex.norm_exp`),
  which is what lets the imaginary slope `i * psi * t` rotate without
  entering the error.
-/

-- ## §1 rational pair list operations

def complexPolyAdd2647 : List RatPair2542 → List RatPair2542 → List RatPair2542
  | [], right => right
  | left, [] => left
  | headLeft :: tailLeft, headRight :: tailRight =>
      pairAdd2542 headLeft headRight :: complexPolyAdd2647 tailLeft tailRight

def complexPolyScale2647 (scalar : RatPair2542) : List RatPair2542 → List RatPair2542
  | [] => []
  | head :: tail => pairMul2542 scalar head :: complexPolyScale2647 scalar tail

def complexPolyMul2647 : List RatPair2542 → List RatPair2542 → List RatPair2542
  | [], _ => []
  | head :: tail, right => complexPolyAdd2647 (complexPolyScale2647 head right)
      ((0, 0) :: complexPolyMul2647 tail right)

def complexPolyDerivative2647 : List RatPair2542 → List RatPair2542
  | [] => []
  | _ :: tail => complexPolyAdd2647 tail ((0, 0) :: complexPolyDerivative2647 tail)

def complexPolyEvalRat2647 (position : ℚ) : List RatPair2542 → RatPair2542
  | [] => (0, 0)
  | head :: tail =>
      pairAdd2542 head (pairScale2542 position (complexPolyEvalRat2647 position tail))

def complexPolyAbsBound2647 (halfWidth : ℚ) : List RatPair2542 → ℚ
  | [] => 0
  | head :: tail =>
      pairMagnitude2542 head + halfWidth * complexPolyAbsBound2647 halfWidth tail

-- ## §2 evaluation as a ℂ-valued function

noncomputable def complexPolyEval2647 (coefficients : List RatPair2542)
    (position : ℝ) : ℂ :=
  match coefficients with
  | [] => 0
  | head :: tail =>
      embedPair2542 head + position * complexPolyEval2647 tail position

theorem embedPair_zero2647 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> simp [embedPair2542]

theorem complexPolyEval2647_add (left right : List RatPair2542) (position : ℝ) :
    complexPolyEval2647 (complexPolyAdd2647 left right) position =
      complexPolyEval2647 left position + complexPolyEval2647 right position := by
  induction left generalizing right with
  | nil => cases right <;> simp [complexPolyAdd2647, complexPolyEval2647]
  | cons head tail ih =>
    cases right with
    | nil => simp [complexPolyAdd2647, complexPolyEval2647]
    | cons headRight tailRight =>
      simp only [complexPolyAdd2647, complexPolyEval2647, ih, embedPair_add2542]
      ring

theorem complexPolyEval2647_scale (scalar : RatPair2542) (coefficients : List RatPair2542)
    (position : ℝ) :
    complexPolyEval2647 (complexPolyScale2647 scalar coefficients) position =
      embedPair2542 scalar * complexPolyEval2647 coefficients position := by
  induction coefficients with
  | nil => simp [complexPolyScale2647, complexPolyEval2647]
  | cons head tail ih =>
    simp only [complexPolyScale2647, complexPolyEval2647, embedPair_mul2542, ih]
    ring

theorem complexPolyEval2647_mul (left right : List RatPair2542) (position : ℝ) :
    complexPolyEval2647 (complexPolyMul2647 left right) position =
      complexPolyEval2647 left position * complexPolyEval2647 right position := by
  induction left with
  | nil => simp [complexPolyMul2647, complexPolyEval2647]
  | cons head tail ih =>
    simp only [complexPolyMul2647, complexPolyEval2647_add, complexPolyEval2647_scale,
      complexPolyEval2647, embedPair_zero2647, zero_add, ih]
    ring

theorem complexPolyEval2647_hasDerivAt (coefficients : List RatPair2542) (position : ℝ) :
    HasDerivAt (complexPolyEval2647 coefficients)
      (complexPolyEval2647 (complexPolyDerivative2647 coefficients) position) position := by
  induction coefficients with
  | nil =>
    simpa [complexPolyEval2647, complexPolyDerivative2647] using
      hasDerivAt_const position (0 : ℂ)
  | cons head tail ih =>
    have hmul : HasDerivAt (fun x => (x : ℝ) * complexPolyEval2647 tail x)
        (complexPolyEval2647 tail position +
          (position : ℝ) *
            complexPolyEval2647 (complexPolyDerivative2647 tail) position) position := by
      have h := HasDerivAt.smul (hasDerivAt_id position) ih
      simpa only [Pi.smul_apply, id_eq, one_smul, Complex.real_smul, add_comm] using h
    have h := (hasDerivAt_const position (embedPair2542 head)).add hmul
    simpa only [complexPolyEval2647, complexPolyDerivative2647, complexPolyEval2647_add,
      embedPair_zero2647, zero_add, add_zero, Pi.add_apply] using h

theorem complexPolyEval2647_cast (coefficients : List RatPair2542) (position : ℚ) :
    complexPolyEval2647 coefficients (position : ℝ) =
      embedPair2542 (complexPolyEvalRat2647 position coefficients) := by
  have hq : ((position : ℚ) : ℂ) = (((position : ℚ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  induction coefficients with
  | nil => simp [complexPolyEval2647, complexPolyEvalRat2647, embedPair_zero2647]
  | cons head tail ih =>
    simp only [complexPolyEval2647, complexPolyEvalRat2647, ih, embedPair_add2542,
      embedPair_scale2542, hq]

theorem complexPolyAbsBound2647_nonneg (coefficients : List RatPair2542) (halfWidth : ℚ)
    (hwidth : 0 ≤ halfWidth) : 0 ≤ complexPolyAbsBound2647 halfWidth coefficients := by
  induction coefficients with
  | nil => simp [complexPolyAbsBound2647]
  | cons head tail ih =>
    simp only [complexPolyAbsBound2647]
    refine add_nonneg ?_ (mul_nonneg hwidth ih)
    change 0 ≤ |head.1| + |head.2|
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem complexPolyEval2647_abs_le (coefficients : List RatPair2542) (halfWidth : ℚ)
    (hwidth : 0 ≤ halfWidth) (position : ℝ)
    (hposition : |position| ≤ (halfWidth : ℝ)) :
    ‖complexPolyEval2647 coefficients position‖ ≤
      (complexPolyAbsBound2647 halfWidth coefficients : ℝ) := by
  induction coefficients with
  | nil => simp [complexPolyEval2647, complexPolyAbsBound2647]
  | cons head tail ih =>
    rw [complexPolyEval2647]
    calc ‖embedPair2542 head + position * complexPolyEval2647 tail position‖
        ≤ ‖embedPair2542 head‖ + |position| * ‖complexPolyEval2647 tail position‖ :=
          by simpa using norm_add_le (embedPair2542 head)
              (position * complexPolyEval2647 tail position)
      _ ≤ (pairMagnitude2542 head : ℝ) +
            (halfWidth : ℝ) * (complexPolyAbsBound2647 halfWidth tail : ℝ) := by
          refine add_le_add (embedPair_magnitude2542 head) ?_
          calc |position| * ‖complexPolyEval2647 tail position‖ ≤
              (halfWidth : ℝ) * ‖complexPolyEval2647 tail position‖ :=
            mul_le_mul_of_nonneg_right hposition (norm_nonneg _)
            _ ≤ (halfWidth : ℝ) * (complexPolyAbsBound2647 halfWidth tail : ℝ) :=
            mul_le_mul_of_nonneg_left ih (Rat.cast_nonneg.mpr hwidth)
      _ = (complexPolyAbsBound2647 halfWidth (head :: tail) : ℝ) := by
          simp [complexPolyAbsBound2647]

-- ## §3 complex residual stability

theorem complexExpPolynomialResidualStability2647
    (phase phaseDerivative polynomial polynomialDerivative : ℝ → ℂ)
    (halfWidth variation residualUpper : ℝ) (hwidth : 0 ≤ halfWidth)
    (hpolynomialZero : polynomial 0 = 1)
    (hphaseDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt phase (phaseDerivative position) position)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hreVariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |(phase position - phase 0).re| ≤ variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      ‖polynomialDerivative position - phaseDerivative position * polynomial position‖
        ≤ residualUpper)
    (position : ℝ) (hposition : position ∈ Icc (-halfWidth) halfWidth) :
    ‖Complex.exp (phase position - phase 0) - polynomial position‖ ≤
      Real.exp (2 * variation) * residualUpper * |position| := by
  let adjusted : ℝ → ℂ := fun coordinate =>
    polynomial coordinate * Complex.exp (phase 0 - phase coordinate)
  have hreExp : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      ‖Complex.exp (phase 0 - phase coordinate)‖ ≤ Real.exp variation := by
    intro coordinate hcoordinate
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hv := hreVariation coordinate hcoordinate
    have hflip : (phase 0 - phase coordinate).re = -((phase coordinate - phase 0).re) := by
      rw [Complex.sub_re, Complex.sub_re]; ring
    rw [hflip]
    linarith [abs_le.mp hv]
  have hderivative : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt adjusted
        (Complex.exp (phase 0 - phase coordinate) *
          (polynomialDerivative coordinate -
            phaseDerivative coordinate * polynomial coordinate)) coordinate := by
    intro coordinate hcoordinate
    have hsub : HasDerivAt (fun x => phase 0 - phase x)
        (-(phaseDerivative coordinate)) coordinate := by
      simpa using (hasDerivAt_const coordinate (phase 0)).sub
        (hphaseDerivative coordinate hcoordinate)
    have hexpDeriv : HasDerivAt (fun x => Complex.exp (phase 0 - phase x))
        (Complex.exp (phase 0 - phase coordinate) *
          (-(phaseDerivative coordinate))) coordinate := by
      have raw := HasDerivAt.comp coordinate
        (Complex.hasDerivAt_exp (phase 0 - phase coordinate)) hsub
      simpa [Function.comp, smul_eq_mul] using raw
    have h := (hpolynomialDerivative coordinate hcoordinate).mul hexpDeriv
    convert h using 1
    dsimp [adjusted]
    ring
  have hbound : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      ‖Complex.exp (phase 0 - phase coordinate) *
        (polynomialDerivative coordinate -
          phaseDerivative coordinate * polynomial coordinate)‖ ≤
        Real.exp variation * residualUpper := by
    intro coordinate hcoordinate
    rw [norm_mul]
    exact mul_le_mul (hreExp coordinate hcoordinate) (hresidual coordinate hcoordinate)
      (norm_nonneg _) (le_of_lt (Real.exp_pos _))
  have hzero : (0 : ℝ) ∈ Icc (-halfWidth) halfWidth := ⟨by linarith, hwidth⟩
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun coordinate hcoordinate => (hderivative coordinate hcoordinate).hasDerivWithinAt)
    hbound (convex_Icc (-halfWidth) halfWidth) hzero hposition
  have hadjustedZero : adjusted 0 = 1 := by
    dsimp [adjusted]
    rw [hpolynomialZero, sub_self, Complex.exp_zero, mul_one]
  rw [hadjustedZero, norm_sub_rev, Real.norm_eq_abs, sub_zero] at hmean
  have hforward : ‖Complex.exp (phase position - phase 0)‖ ≤ Real.exp variation := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    linarith [abs_le.mp (hreVariation position hposition)]
  have hexpProduct : Complex.exp (phase position - phase 0) *
      Complex.exp (phase 0 - phase position) = 1 := by
    rw [← Complex.exp_add, sub_add_sub_cancel, sub_self, Complex.exp_zero]
  have hfactor : Complex.exp (phase position - phase 0) - polynomial position =
      Complex.exp (phase position - phase 0) * (1 - adjusted position) := by
    dsimp only [adjusted]
    rw [mul_sub, mul_one, ← mul_assoc, mul_right_comm, hexpProduct]
    ring
  have hsplit : ‖Complex.exp (phase position - phase 0) - polynomial position‖ ≤
      Real.exp variation * ‖1 - adjusted position‖ := by
    rw [hfactor, norm_mul]
    exact mul_le_mul_of_nonneg_right hforward (norm_nonneg _)
  calc ‖Complex.exp (phase position - phase 0) - polynomial position‖
      ≤ Real.exp variation * ‖1 - adjusted position‖ := hsplit
    _ ≤ Real.exp variation * (Real.exp variation * residualUpper * |position|) :=
      mul_le_mul_of_nonneg_left hmean (le_of_lt (Real.exp_pos _))
    _ = Real.exp (2 * variation) * residualUpper * |position| := by
      rw [show (2 : ℝ) * variation = variation + variation by ring, Real.exp_add]
      ring

end ConnesWeilRH.Dev
