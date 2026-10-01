import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget
import Mathlib.Analysis.Complex.CauchyIntegral

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped Interval

noncomputable def tailContourIntegrand2353 (radius : ℝ) (sourcePoint point : ℂ) : ℂ :=
  Complex.exp ((-30 : ℂ) / (1 - point ^ 2) + sourcePoint * (radius : ℂ) * point)

theorem tailContourIntegrand2353_differentiableAt (radius : ℝ) (sourcePoint point : ℂ)
    (hstrip : |point.re| < 1) :
    DifferentiableAt ℂ (tailContourIntegrand2353 radius sourcePoint) point := by
  have hparts := abs_lt.mp hstrip
  have hpositive : 0 < (1 - point ^ 2).re := by
    simp only [pow_two, Complex.sub_re, Complex.one_re, Complex.mul_re]
    have hproduct : 0 < (1 - point.re) * (1 + point.re) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg point.im]
  have hdenominator : (1 : ℂ) - point ^ 2 ≠ 0 := by
    intro hzero
    rw [hzero] at hpositive
    simp at hpositive
  have hquotient : DifferentiableAt ℂ (fun inputPoint : ℂ => (-30 : ℂ) / (1 - inputPoint ^ 2))
      point := (differentiableAt_const (-30 : ℂ)).div
        ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.pow 2)) hdenominator
  have hlinear : DifferentiableAt ℂ
      (fun inputPoint : ℂ => sourcePoint * (radius : ℂ) * inputPoint) point :=
    (differentiableAt_const (sourcePoint * (radius : ℂ))).mul differentiableAt_id
  exact (hquotient.add hlinear).cexp

theorem tailContour_norm_eq2353 (radius sigma height realPart imagPart : ℝ) :
    ‖tailContourIntegrand2353 radius ((sigma : ℂ) + (height : ℂ) * Complex.I)
        ((realPart : ℂ) + (imagPart : ℂ) * Complex.I)‖ =
      Real.exp (-30 * (1 - realPart ^ 2 + imagPart ^ 2) /
        ((1 - realPart ^ 2 + imagPart ^ 2) ^ 2 + 4 * realPart ^ 2 * imagPart ^ 2) +
        radius * (sigma * realPart - height * imagPart)) := by
  unfold tailContourIntegrand2353
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.div_re, Complex.normSq, pow_two]
  ring

theorem weightedFamily_eq_tailContour2353 (coefficient sourcePoint : ℂ)
    (modulation radius coordinate : ℝ) (hradius : 0 < radius) (hcoordinate : |coordinate| < 1) :
    Complex.exp (sourcePoint * (radius * coordinate : ℝ)) *
        externalFamilyValue2344 coefficient modulation radius (radius * coordinate) =
      coefficient * tailContourIntegrand2353 radius
        (sourcePoint + (modulation : ℂ) * Complex.I) (coordinate : ℂ) := by
  have hinside : |radius * coordinate| < radius := by
    rw [abs_mul, abs_of_pos hradius]
    simpa using mul_lt_mul_of_pos_left hcoordinate hradius
  have hratio : radius * coordinate / radius = coordinate := by
    field_simp [hradius.ne']
  rw [externalFamilyValue2344, if_pos hinside, hratio]
  calc
    _ = coefficient * Complex.exp (sourcePoint * (radius * coordinate : ℝ) +
        ((-30 / (1 - coordinate ^ 2) : ℝ) +
          (modulation * (radius * coordinate) : ℝ) * Complex.I)) := by
      simp only [Complex.exp_add]
      ring
    _ = _ := by
      unfold tailContourIntegrand2353
      congr 2
      push_cast
      ring

theorem tailContour_rectangle_eq_zero2353 (radius : ℝ) (sourcePoint : ℂ)
    (cut shift : ℝ) (hcut : 0 ≤ cut) (hcutOne : cut < 1) :
    (∫ coordinate : ℝ in -cut..cut,
      tailContourIntegrand2353 radius sourcePoint (coordinate : ℂ)) -
    (∫ coordinate : ℝ in -cut..cut,
      tailContourIntegrand2353 radius sourcePoint
        ((coordinate : ℂ) + (shift : ℂ) * Complex.I)) +
    Complex.I * (∫ height : ℝ in 0..shift,
      tailContourIntegrand2353 radius sourcePoint ((cut : ℂ) + (height : ℂ) * Complex.I)) -
    Complex.I * (∫ height : ℝ in 0..shift,
      tailContourIntegrand2353 radius sourcePoint ((-cut : ℂ) + (height : ℂ) * Complex.I)) = 0 := by
  have horder : -cut ≤ cut := by linarith
  have hd : DifferentiableOn ℂ (tailContourIntegrand2353 radius sourcePoint)
      ([[(-cut : ℂ).re, ((cut : ℂ) + (shift : ℂ) * Complex.I).re]] ×ℂ
        [[(-cut : ℂ).im, ((cut : ℂ) + (shift : ℂ) * Complex.I).im]]) := by
    intro point hpoint
    have hreal : point.re ∈ Set.Icc (-cut) cut := by
      simpa [Set.uIcc_of_le horder] using hpoint.1
    apply (tailContourIntegrand2353_differentiableAt
      radius sourcePoint point _).differentiableWithinAt
    exact abs_lt.mpr ⟨by linarith [hreal.1], by linarith [hreal.2]⟩
  have hrectangle := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (tailContourIntegrand2353 radius sourcePoint) (-cut : ℂ)
    ((cut : ℂ) + (shift : ℂ) * Complex.I) hd
  simpa using hrectangle

end ConnesWeilRH.Dev
