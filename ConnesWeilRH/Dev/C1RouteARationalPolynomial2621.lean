import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

def polynomialAdd2621 : List ℚ → List ℚ → List ℚ
  | [], right => right
  | left, [] => left
  | headLeft :: tailLeft, headRight :: tailRight =>
      (headLeft + headRight) :: polynomialAdd2621 tailLeft tailRight

def polynomialScale2621 (scalar : ℚ) : List ℚ → List ℚ
  | [] => []
  | head :: tail => scalar * head :: polynomialScale2621 scalar tail

def polynomialMul2621 : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | head :: tail, right => polynomialAdd2621 (polynomialScale2621 head right)
      (0 :: polynomialMul2621 tail right)

def polynomialDerivative2621 : List ℚ → List ℚ
  | [] => []
  | _ :: tail => polynomialAdd2621 tail (0 :: polynomialDerivative2621 tail)

def polynomialEvalRat2621 (position : ℚ) : List ℚ → ℚ
  | [] => 0
  | head :: tail => head + position * polynomialEvalRat2621 position tail

noncomputable def polynomialEval2621 (coefficients : List ℚ) (position : ℝ) : ℝ :=
  match coefficients with
  | [] => 0
  | head :: tail => (head : ℝ) + position * polynomialEval2621 tail position

def polynomialAbsBound2621 (halfWidth : ℚ) : List ℚ → ℚ
  | [] => 0
  | head :: tail => |head| + halfWidth * polynomialAbsBound2621 halfWidth tail

theorem polynomialEval_add2621 (left right : List ℚ) (position : ℝ) :
    polynomialEval2621 (polynomialAdd2621 left right) position =
      polynomialEval2621 left position + polynomialEval2621 right position := by
  induction left generalizing right with
  | nil => simp [polynomialAdd2621, polynomialEval2621]
  | cons head tail ih =>
    cases right with
    | nil => simp [polynomialAdd2621, polynomialEval2621]
    | cons headRight tailRight =>
      simp only [polynomialAdd2621, polynomialEval2621, ih, Rat.cast_add]
      ring

theorem polynomialEval_scale2621 (scalar : ℚ) (coefficients : List ℚ) (position : ℝ) :
    polynomialEval2621 (polynomialScale2621 scalar coefficients) position =
      (scalar : ℝ) * polynomialEval2621 coefficients position := by
  induction coefficients with
  | nil => simp [polynomialScale2621, polynomialEval2621]
  | cons head tail ih =>
    simp only [polynomialScale2621, polynomialEval2621, Rat.cast_mul, ih]
    ring

theorem polynomialEval_mul2621 (left right : List ℚ) (position : ℝ) :
    polynomialEval2621 (polynomialMul2621 left right) position =
      polynomialEval2621 left position * polynomialEval2621 right position := by
  induction left with
  | nil => simp [polynomialMul2621, polynomialEval2621]
  | cons head tail ih =>
    simp only [polynomialMul2621, polynomialEval_add2621, polynomialEval_scale2621,
      polynomialEval2621, Rat.cast_zero, zero_add, ih]
    ring

theorem polynomialEval_hasDerivAt2621 (coefficients : List ℚ) (position : ℝ) :
    HasDerivAt (polynomialEval2621 coefficients)
      (polynomialEval2621 (polynomialDerivative2621 coefficients) position) position := by
  induction coefficients with
  | nil => simpa [polynomialEval2621, polynomialDerivative2621] using
      hasDerivAt_const position (0 : ℝ)
  | cons head tail ih =>
    have h := (hasDerivAt_const position (head : ℝ)).add ((hasDerivAt_id position).mul ih)
    simpa only [polynomialEval2621, polynomialDerivative2621, polynomialEval_add2621,
      Rat.cast_zero, zero_add, one_mul, Pi.add_apply, Pi.mul_apply, id_eq] using h

theorem polynomialEval_cast2621 (coefficients : List ℚ) (position : ℚ) :
    polynomialEval2621 coefficients (position : ℝ) =
      (polynomialEvalRat2621 position coefficients : ℝ) := by
  induction coefficients with
  | nil => simp [polynomialEval2621, polynomialEvalRat2621]
  | cons head tail ih =>
    simp [polynomialEval2621, polynomialEvalRat2621, ih]

theorem polynomialAbsBound_nonneg2621 (coefficients : List ℚ) (halfWidth : ℚ)
    (hwidth : 0 ≤ halfWidth) : 0 ≤ polynomialAbsBound2621 halfWidth coefficients := by
  induction coefficients with
  | nil => simp [polynomialAbsBound2621]
  | cons head tail ih =>
    exact add_nonneg (abs_nonneg head) (mul_nonneg hwidth ih)

theorem polynomialEval_abs_le2621 (coefficients : List ℚ) (halfWidth : ℚ)
    (hwidth : 0 ≤ halfWidth) (position : ℝ) (hposition : |position| ≤ (halfWidth : ℝ)) :
    |polynomialEval2621 coefficients position| ≤
      (polynomialAbsBound2621 halfWidth coefficients : ℝ) := by
  induction coefficients with
  | nil => simp [polynomialEval2621, polynomialAbsBound2621]
  | cons head tail ih =>
    calc
      _ ≤ |(head : ℝ)| + |position * polynomialEval2621 tail position| := abs_add_le _ _
      _ = |(head : ℝ)| + |position| * |polynomialEval2621 tail position| := by rw [abs_mul]
      _ ≤ |(head : ℝ)| + (halfWidth : ℝ) *
          (polynomialAbsBound2621 halfWidth tail : ℝ) :=
        add_le_add (le_refl _) (mul_le_mul hposition ih (abs_nonneg _)
          (Rat.cast_nonneg.mpr hwidth))
      _ = _ := by simp [polynomialAbsBound2621]

theorem polynomialEval_integral2621 (coefficients primitive : List ℚ)
    (hderivative : polynomialDerivative2621 primitive = coefficients) (lower upper : ℚ) :
    (∫ position in (lower : ℝ)..(upper : ℝ), polynomialEval2621 coefficients position) =
      ((polynomialEvalRat2621 upper primitive - polynomialEvalRat2621 lower primitive : ℚ) : ℝ) := by
  have hintegrable : IntervalIntegrable (polynomialEval2621 coefficients)
      MeasureTheory.volume (lower : ℝ) (upper : ℝ) :=
    (continuous_iff_continuousAt.mpr (fun position =>
      (polynomialEval_hasDerivAt2621 coefficients position).continuousAt)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun position _ => hderivative ▸ polynomialEval_hasDerivAt2621 primitive position) hintegrable
  simpa only [polynomialEval_cast2621, Rat.cast_sub] using h

end ConnesWeilRH.Dev
