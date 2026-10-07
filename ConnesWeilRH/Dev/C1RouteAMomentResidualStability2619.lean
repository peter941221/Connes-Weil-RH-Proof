import ConnesWeilRH.Dev.C1RouteAAnalyticMomentNormalization2618
import Mathlib.Analysis.Calculus.MeanValue

namespace ConnesWeilRH.Dev

open Set

noncomputable def momentPhase2619 (beta center position : ℝ) : ℝ :=
  -30 / (1 - (center + position) ^ 2) + beta * (center + position)

noncomputable def momentPhaseDerivative2619 (beta center position : ℝ) : ℝ :=
  beta - 60 * (center + position) / (1 - (center + position) ^ 2) ^ 2

noncomputable def momentPhaseSlopeUpper2619 (beta center halfWidth : ℝ) : ℝ :=
  |beta| + 60 * (|center| + halfWidth) / (1 - (|center| + halfWidth) ^ 2) ^ 2

theorem momentPhase2619_hasDerivAt (beta center position : ℝ)
    (hdeficit : 1 - (center + position) ^ 2 ≠ 0) :
    HasDerivAt (momentPhase2619 beta center) (momentPhaseDerivative2619 beta center position)
      position := by
  have hlinear := (hasDerivAt_const position center).add (hasDerivAt_id position)
  have hdenominator := (hasDerivAt_const position (1 : ℝ)).sub (hlinear.pow 2)
  have hquotient := (hasDerivAt_const position (-30 : ℝ)).div hdenominator hdeficit
  have hsum := hquotient.add (hlinear.const_mul beta)
  convert hsum using 1
  dsimp [momentPhase2619, momentPhaseDerivative2619]
  field_simp [hdeficit]
  ring

theorem realNormalizedMomentIntegrand2618_eq_phase2619
    (radius nodeReal center position : ℝ) (hinside : |center + position| < 1) :
    realNormalizedMomentIntegrand2618 radius nodeReal (center + position) =
      Real.exp (momentPhase2619 (nodeReal * radius) center position) := by
  simp only [realNormalizedMomentIntegrand2618, if_pos hinside, momentPhase2619]

theorem momentPanel_interior2619 (center halfWidth position : ℝ)
    (hgeometry : |center| + halfWidth < 1)
    (hposition : position ∈ Icc (-halfWidth) halfWidth) : |center + position| < 1 := by
  exact ((abs_add_le center position).trans
    (add_le_add (le_refl |center|) (abs_le.mpr hposition))).trans_lt hgeometry

theorem momentPhaseDerivative2619_le_slopeUpper (beta center halfWidth position : ℝ)
    (hwidth : 0 ≤ halfWidth) (hgeometry : |center| + halfWidth < 1)
    (hposition : position ∈ Icc (-halfWidth) halfWidth) :
    |momentPhaseDerivative2619 beta center position| ≤
      momentPhaseSlopeUpper2619 beta center halfWidth := by
  have hedge : 0 ≤ |center| + halfWidth := add_nonneg (abs_nonneg _) hwidth
  have hcoordinate : |center + position| ≤ |center| + halfWidth :=
    (abs_add_le center position).trans (add_le_add (le_refl |center|) (abs_le.mpr hposition))
  have hdeficit : 0 < 1 - (|center| + halfWidth) ^ 2 := by
    nlinarith
  have hdeficitComparison : 1 - (|center| + halfWidth) ^ 2 ≤ 1 - (center + position) ^ 2 := by
    nlinarith [sq_abs (center + position), abs_nonneg (center + position)]
  have hdenominatorPositive : 0 < (1 - (center + position) ^ 2) ^ 2 :=
    sq_pos_of_pos (hdeficit.trans_le hdeficitComparison)
  have hdenominatorLower : (1 - (|center| + halfWidth) ^ 2) ^ 2 ≤
      (1 - (center + position) ^ 2) ^ 2 := by
    nlinarith
  have hquotient : |60 * (center + position) / (1 - (center + position) ^ 2) ^ 2| ≤
      60 * (|center| + halfWidth) / (1 - (|center| + halfWidth) ^ 2) ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hdenominatorPositive]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 60)]
    calc
      _ ≤ 60 * (|center| + halfWidth) / (1 - (center + position) ^ 2) ^ 2 :=
        (div_le_div_iff_of_pos_right hdenominatorPositive).mpr
          (mul_le_mul_of_nonneg_left hcoordinate (by norm_num))
      _ ≤ 60 * (|center| + halfWidth) / (1 - (|center| + halfWidth) ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hdeficit) hdenominatorLower
  have htriangle : |beta - 60 * (center + position) / (1 - (center + position) ^ 2) ^ 2| ≤
      |beta| + |60 * (center + position) / (1 - (center + position) ^ 2) ^ 2| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le beta
      (60 * (center + position) / (1 - (center + position) ^ 2) ^ 2)
  exact htriangle.trans (add_le_add (le_refl |beta|) hquotient)

theorem momentPhase2619_variation_le (beta center halfWidth position : ℝ)
    (hwidth : 0 ≤ halfWidth) (hgeometry : |center| + halfWidth < 1)
    (hposition : position ∈ Icc (-halfWidth) halfWidth) :
    |momentPhase2619 beta center position - momentPhase2619 beta center 0| ≤
      momentPhaseSlopeUpper2619 beta center halfWidth * halfWidth := by
  have hderivative : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      HasDerivWithinAt (momentPhase2619 beta center)
        (momentPhaseDerivative2619 beta center coordinate) (Icc (-halfWidth) halfWidth) coordinate := by
    intro coordinate hcoordinate
    have hsmall := (sq_lt_one_iff_abs_lt_one (center + coordinate)).mpr
      (momentPanel_interior2619 center halfWidth coordinate hgeometry hcoordinate)
    exact (momentPhase2619_hasDerivAt beta center coordinate (by linarith)).hasDerivWithinAt
  have hbound : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      ‖momentPhaseDerivative2619 beta center coordinate‖ ≤
        momentPhaseSlopeUpper2619 beta center halfWidth := by
    intro coordinate hcoordinate
    rw [Real.norm_eq_abs]
    exact momentPhaseDerivative2619_le_slopeUpper beta center halfWidth coordinate
      hwidth hgeometry hcoordinate
  have hzero : (0 : ℝ) ∈ Icc (-halfWidth) halfWidth := ⟨by linarith, hwidth⟩
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderivative hbound
    (convex_Icc (-halfWidth) halfWidth) hzero hposition
  rw [Real.norm_eq_abs, sub_zero, Real.norm_eq_abs] at hmean
  apply hmean.trans
  exact mul_le_mul_of_nonneg_left (abs_le.mpr hposition) (by
    dsimp [momentPhaseSlopeUpper2619]
    positivity)

theorem exp_polynomial_residual_stability2619
    (phase phaseDerivative polynomial polynomialDerivative : ℝ → ℝ)
    (halfWidth variation residualUpper : ℝ) (hwidth : 0 ≤ halfWidth)
    (hpolynomialZero : polynomial 0 = 1)
    (hphaseDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt phase (phaseDerivative position) position)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hvariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |phase position - phase 0| ≤ variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |polynomialDerivative position - phaseDerivative position * polynomial position| ≤ residualUpper)
    (position : ℝ) (hposition : position ∈ Icc (-halfWidth) halfWidth) :
    |Real.exp (phase position - phase 0) - polynomial position| ≤
      Real.exp (2 * variation) * residualUpper * |position| := by
  let adjusted : ℝ → ℝ := fun coordinate =>
    polynomial coordinate * Real.exp (phase 0 - phase coordinate)
  let adjustedDerivative : ℝ → ℝ := fun coordinate =>
    Real.exp (phase 0 - phase coordinate) *
      (polynomialDerivative coordinate - phaseDerivative coordinate * polynomial coordinate)
  have hderivative : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt adjusted (adjustedDerivative coordinate) coordinate := by
    intro coordinate hcoordinate
    have h := (hpolynomialDerivative coordinate hcoordinate).mul
      (((hasDerivAt_const coordinate (phase 0)).sub
        (hphaseDerivative coordinate hcoordinate)).exp)
    convert h using 1
    dsimp [adjustedDerivative, adjusted]
    ring
  have hbound : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      ‖adjustedDerivative coordinate‖ ≤ Real.exp variation * residualUpper := by
    intro coordinate hcoordinate
    have hinverse : Real.exp (phase 0 - phase coordinate) ≤ Real.exp variation := by
      apply Real.exp_le_exp.mpr
      have h := (abs_le.mp (hvariation coordinate hcoordinate)).1
      linarith
    dsimp [adjustedDerivative]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hinverse (hresidual coordinate hcoordinate) (abs_nonneg _)
      (le_of_lt (Real.exp_pos _))
  have hzero : (0 : ℝ) ∈ Icc (-halfWidth) halfWidth := ⟨by linarith, hwidth⟩
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun coordinate hcoordinate => (hderivative coordinate hcoordinate).hasDerivWithinAt)
    hbound (convex_Icc (-halfWidth) halfWidth) hzero hposition
  have hadjustedZero : adjusted 0 = 1 := by simp [adjusted, hpolynomialZero]
  rw [hadjustedZero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmean
  have hforward : Real.exp (phase position - phase 0) ≤ Real.exp variation :=
    Real.exp_le_exp.mpr (abs_le.mp (hvariation position hposition)).2
  have hproduct : Real.exp (phase position - phase 0) *
      Real.exp (phase 0 - phase position) = 1 := by
    rw [← Real.exp_add]
    rw [sub_add_sub_cancel, sub_self, Real.exp_zero]
  have hequality : Real.exp (phase position - phase 0) - polynomial position =
      Real.exp (phase position - phase 0) * (1 - adjusted position) := by
    dsimp [adjusted]
    rw [mul_sub, mul_one, mul_left_comm, hproduct, mul_one]
  rw [hequality, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
  calc
    _ ≤ Real.exp variation * (Real.exp variation * residualUpper * |position|) :=
      mul_le_mul hforward hmean (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    _ = Real.exp (2 * variation) * residualUpper * |position| := by
      rw [show (2 : ℝ) * variation = variation + variation by ring, Real.exp_add]
      ring

theorem momentPhase_polynomial_residual_stability2619
    (beta center : ℝ) (polynomial polynomialDerivative : ℝ → ℝ)
    (halfWidth variation residualUpper : ℝ) (hwidth : 0 ≤ halfWidth)
    (hpolynomialZero : polynomial 0 = 1)
    (hinterior : ∀ position ∈ Icc (-halfWidth) halfWidth, |center + position| < 1)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hvariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |momentPhase2619 beta center position - momentPhase2619 beta center 0| ≤ variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |polynomialDerivative position - momentPhaseDerivative2619 beta center position *
        polynomial position| ≤ residualUpper)
    (position : ℝ) (hposition : position ∈ Icc (-halfWidth) halfWidth) :
    |Real.exp (momentPhase2619 beta center position) -
      Real.exp (momentPhase2619 beta center 0) * polynomial position| ≤
      Real.exp (momentPhase2619 beta center 0) *
        (Real.exp (2 * variation) * residualUpper * |position|) := by
  have hphaseDerivative : ∀ coordinate ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt (momentPhase2619 beta center)
        (momentPhaseDerivative2619 beta center coordinate) coordinate := by
    intro coordinate hcoordinate
    apply momentPhase2619_hasDerivAt
    have hsmall := (sq_lt_one_iff_abs_lt_one (center + coordinate)).mpr
      (hinterior coordinate hcoordinate)
    linarith
  have h := exp_polynomial_residual_stability2619
    (momentPhase2619 beta center) (momentPhaseDerivative2619 beta center)
    polynomial polynomialDerivative halfWidth variation residualUpper hwidth
    hpolynomialZero hphaseDerivative hpolynomialDerivative
    hvariation hresidual position hposition
  have hequality : Real.exp (momentPhase2619 beta center position) -
      Real.exp (momentPhase2619 beta center 0) * polynomial position =
      Real.exp (momentPhase2619 beta center 0) *
        (Real.exp (momentPhase2619 beta center position - momentPhase2619 beta center 0) -
          polynomial position) := by
    rw [mul_sub, ← Real.exp_add]
    congr 2
    ring
  rw [hequality, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos _))

noncomputable def momentPolynomialResidual2619
    (beta center : ℝ) (polynomial polynomialDerivative : ℝ → ℝ) (position : ℝ) : ℝ :=
  (1 - (center + position) ^ 2) ^ 2 * polynomialDerivative position -
    (beta * (1 - (center + position) ^ 2) ^ 2 - 60 * (center + position)) *
      polynomial position

theorem momentDerivativeResidual_eq_polynomialQuotient2619
    (beta center : ℝ) (polynomial polynomialDerivative : ℝ → ℝ) (position : ℝ)
    (hdeficit : 1 - (center + position) ^ 2 ≠ 0) :
    polynomialDerivative position - momentPhaseDerivative2619 beta center position *
      polynomial position =
        momentPolynomialResidual2619 beta center polynomial polynomialDerivative position /
          (1 - (center + position) ^ 2) ^ 2 := by
  dsimp [momentPolynomialResidual2619, momentPhaseDerivative2619]
  field_simp [hdeficit]

theorem momentDerivativeResidual_le_of_polynomialBound2619
    (beta center : ℝ) (polynomial polynomialDerivative : ℝ → ℝ) (position : ℝ)
    (denominatorLower numeratorUpper : ℝ) (hdenominatorPositive : 0 < denominatorLower)
    (hdenominator : denominatorLower ≤ (1 - (center + position) ^ 2) ^ 2)
    (hnumerator : |momentPolynomialResidual2619 beta center polynomial polynomialDerivative
      position| ≤ numeratorUpper) :
    |polynomialDerivative position - momentPhaseDerivative2619 beta center position *
      polynomial position| ≤ numeratorUpper / denominatorLower := by
  have hdenominatorValue : 0 < (1 - (center + position) ^ 2) ^ 2 :=
    hdenominatorPositive.trans_le hdenominator
  have hdeficit : 1 - (center + position) ^ 2 ≠ 0 := by
    intro hzero
    simp [hzero] at hdenominatorValue
  rw [momentDerivativeResidual_eq_polynomialQuotient2619 _ _ _ _ _ hdeficit,
    abs_div, abs_of_pos hdenominatorValue]
  calc
    _ ≤ numeratorUpper / (1 - (center + position) ^ 2) ^ 2 :=
      (div_le_div_iff_of_pos_right hdenominatorValue).mpr hnumerator
    _ ≤ numeratorUpper / denominatorLower :=
      div_le_div_of_nonneg_left ((abs_nonneg _).trans hnumerator)
        hdenominatorPositive hdenominator

theorem momentPhase_polynomial_integral_error2619
    (beta center : ℝ) (polynomial polynomialDerivative : ℝ → ℝ)
    (halfWidth variation residualUpper : ℝ) (hwidth : 0 ≤ halfWidth)
    (hresidualNonneg : 0 ≤ residualUpper) (hpolynomialZero : polynomial 0 = 1)
    (hinterior : ∀ position ∈ Icc (-halfWidth) halfWidth, |center + position| < 1)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hvariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |momentPhase2619 beta center position - momentPhase2619 beta center 0| ≤ variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |polynomialDerivative position - momentPhaseDerivative2619 beta center position *
        polynomial position| ≤ residualUpper) :
    |(∫ position in (-halfWidth)..halfWidth, Real.exp (momentPhase2619 beta center position)) -
      Real.exp (momentPhase2619 beta center 0) *
        (∫ position in (-halfWidth)..halfWidth, polynomial position)| ≤
      Real.exp (momentPhase2619 beta center 0) * Real.exp (2 * variation) *
        residualUpper * (2 * halfWidth ^ 2) := by
  have horder : -halfWidth ≤ halfWidth := by linarith
  have hphaseContinuous : ContinuousOn (momentPhase2619 beta center)
      (Icc (-halfWidth) halfWidth) := by
    intro position hposition
    have hsmall := (sq_lt_one_iff_abs_lt_one (center + position)).mpr
      (hinterior position hposition)
    exact (momentPhase2619_hasDerivAt beta center position (by linarith)).continuousAt.continuousWithinAt
  have hpolynomialContinuous : ContinuousOn polynomial (Icc (-halfWidth) halfWidth) :=
    fun position hposition => (hpolynomialDerivative position hposition).continuousAt.continuousWithinAt
  have hexpIntegrable : IntervalIntegrable
      (fun position => Real.exp (momentPhase2619 beta center position))
      MeasureTheory.volume (-halfWidth) halfWidth := by
    simpa only [Function.comp_def] using
      (Real.continuous_exp.comp_continuousOn hphaseContinuous).intervalIntegrable_of_Icc
        horder (μ := MeasureTheory.volume)
  have hpolynomialIntegrable := hpolynomialContinuous.intervalIntegrable_of_Icc horder
    (μ := MeasureTheory.volume)
  have hpointwise : ∀ position ∈ Set.uIoc (-halfWidth) halfWidth,
      ‖Real.exp (momentPhase2619 beta center position) -
        Real.exp (momentPhase2619 beta center 0) * polynomial position‖ ≤
        Real.exp (momentPhase2619 beta center 0) *
          (Real.exp (2 * variation) * residualUpper * halfWidth) := by
    intro position hposition
    rw [Set.uIoc_of_le horder] at hposition
    have hclosed : position ∈ Icc (-halfWidth) halfWidth := ⟨hposition.1.le, hposition.2⟩
    have h := momentPhase_polynomial_residual_stability2619 beta center polynomial
      polynomialDerivative halfWidth variation residualUpper hwidth hpolynomialZero
      hinterior hpolynomialDerivative hvariation hresidual position hclosed
    rw [Real.norm_eq_abs]
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left (abs_le.mpr hclosed)
      (mul_nonneg (le_of_lt (Real.exp_pos _)) hresidualNonneg)
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpointwise
  rw [intervalIntegral.integral_sub hexpIntegrable
      (hpolynomialIntegrable.const_mul (Real.exp (momentPhase2619 beta center 0))),
    intervalIntegral.integral_const_mul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ halfWidth - -halfWidth)] at hintegral
  apply hintegral.trans_eq
  ring

theorem momentPhase_integral_error_of_polynomialResidual2619
    (beta center : ℝ) (polynomial polynomialDerivative : ℝ → ℝ)
    (halfWidth numeratorUpper : ℝ) (hwidth : 0 ≤ halfWidth)
    (hgeometry : |center| + halfWidth < 1) (hnumeratorNonneg : 0 ≤ numeratorUpper)
    (hpolynomialZero : polynomial 0 = 1)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hnumerator : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |momentPolynomialResidual2619 beta center polynomial polynomialDerivative position| ≤ numeratorUpper) :
    |(∫ position in (-halfWidth)..halfWidth, Real.exp (momentPhase2619 beta center position)) -
      Real.exp (momentPhase2619 beta center 0) *
        (∫ position in (-halfWidth)..halfWidth, polynomial position)| ≤
      Real.exp (momentPhase2619 beta center 0) *
        Real.exp (2 * momentPhaseSlopeUpper2619 beta center halfWidth * halfWidth) *
        (numeratorUpper / (1 - (|center| + halfWidth) ^ 2) ^ 2) * (2 * halfWidth ^ 2) := by
  have hedge : 0 ≤ |center| + halfWidth := add_nonneg (abs_nonneg _) hwidth
  have hdeficit : 0 < 1 - (|center| + halfWidth) ^ 2 := by nlinarith
  have hdenominatorPositive : 0 < (1 - (|center| + halfWidth) ^ 2) ^ 2 := sq_pos_of_pos hdeficit
  have hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |polynomialDerivative position - momentPhaseDerivative2619 beta center position *
        polynomial position| ≤ numeratorUpper / (1 - (|center| + halfWidth) ^ 2) ^ 2 := by
    intro position hposition
    have hcoordinate : |center + position| ≤ |center| + halfWidth :=
      (abs_add_le center position).trans (add_le_add (le_refl |center|) (abs_le.mpr hposition))
    have hdeficitComparison : 1 - (|center| + halfWidth) ^ 2 ≤ 1 - (center + position) ^ 2 := by
      nlinarith [sq_abs (center + position), abs_nonneg (center + position)]
    have hdenominator : (1 - (|center| + halfWidth) ^ 2) ^ 2 ≤
        (1 - (center + position) ^ 2) ^ 2 := by nlinarith
    exact momentDerivativeResidual_le_of_polynomialBound2619 beta center polynomial
      polynomialDerivative position _ _ hdenominatorPositive hdenominator (hnumerator position hposition)
  have h := momentPhase_polynomial_integral_error2619 beta center polynomial polynomialDerivative
    halfWidth (momentPhaseSlopeUpper2619 beta center halfWidth * halfWidth)
    (numeratorUpper / (1 - (|center| + halfWidth) ^ 2) ^ 2) hwidth
    (div_nonneg hnumeratorNonneg hdenominatorPositive.le) hpolynomialZero
    (fun position hposition => momentPanel_interior2619 center halfWidth position hgeometry hposition)
    hpolynomialDerivative
    (fun position hposition => momentPhase2619_variation_le beta center halfWidth position
      hwidth hgeometry hposition) hresidual
  simpa only [mul_assoc] using h

end ConnesWeilRH.Dev
