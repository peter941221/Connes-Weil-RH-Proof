import ConnesWeilRH.Dev.C1RouteAExpFamilySecondDerivUpper2510

/-! Record 2512: adapter from the existing interval-data contract.

The old interval theorem supplies the exact exponential curvature bound.  This
adapter replaces that exponential by a certified upper while keeping every
geometric and coefficient premise explicit.
-/

namespace ConnesWeilRH.Dev

theorem weightedExternalFamilySecondDeriv_le_of_interval_exp_upper2512
    (sigma position modulation radius t a coefficientBound upper : ℝ)
    (coefficient : ℂ) (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t)
    (ha : 0 ≤ a) (haone : a < 1) (halower : a ≤ |position / radius|)
    (hcoefficient : ‖coefficient‖ ≤ coefficientBound)
    (hp1 : 0 ≤ 60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|)
    (hp2 : 0 ≤
      (60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
          radius ^ 2) +
        (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
        2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))
    (hupper : Real.exp (-30 / (1 - a ^ 2)) ≤ upper) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      weightedCurvature2348 sigma radius
        (coefficientBound * upper)
        (coefficientBound * upper *
          (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|))
        (coefficientBound * upper *
          ((60 * ((1 - t ^ 2)⁻¹ ^ 2 +
              4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2) +
            (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
            2 * |modulation| *
              (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))) := by
  have hc : 0 ≤ coefficientBound :=
    le_trans (norm_nonneg coefficient) hcoefficient
  have hbase := weightedExternalFamilySecondDeriv_le_of_interval_bounds2488
    sigma position modulation radius t a coefficientBound coefficient
    hradius hinside ht htone hcoord ha haone halower hcoefficient
  have hupper' : Real.exp (-(30 / (1 - a ^ 2))) ≤ upper := by
    simpa [neg_div] using hupper
  have hbase' : ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      weightedCurvature2348 sigma radius
        (coefficientBound * Real.exp (-(30 / (1 - a ^ 2))))
        (coefficientBound * Real.exp (-(30 / (1 - a ^ 2))) *
          (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|))
        (coefficientBound * Real.exp (-(30 / (1 - a ^ 2))) *
          ((60 * ((1 - t ^ 2)⁻¹ ^ 2 +
              4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2) +
            (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
            2 * |modulation| *
              (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))) := by
    simpa [neg_div] using hbase
  exact hbase'.trans (weightedCurvature2348_mono_exp_upper2509
    sigma radius coefficientBound
    (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|)
    ((60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
        radius ^ 2) +
      (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
      2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))
    (30 / (1 - a ^ 2)) upper hc hp1 hp2 hupper')

end ConnesWeilRH.Dev
