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

theorem weightedExternalFamilySecondDeriv_le_of_interval_exp_upper_auto2513
    (sigma position modulation radius t a coefficientBound upper : ℝ)
    (coefficient : ℂ) (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t)
    (ha : 0 ≤ a) (haone : a < 1) (halower : a ≤ |position / radius|)
    (hcoefficient : ‖coefficient‖ ≤ coefficientBound)
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
  have hden : 0 < 1 - t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
  have hp1 : 0 ≤ 60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation| := by
    positivity
  have hp2 : 0 ≤
      (60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
          radius ^ 2) +
        (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
        2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) := by
    positivity
  exact weightedExternalFamilySecondDeriv_le_of_interval_exp_upper2512
    sigma position modulation radius t a coefficientBound upper coefficient
    hradius hinside ht htone hcoord ha haone halower hcoefficient hp1 hp2 hupper

theorem ownerPanelWeightedSecondDeriv_le_sumIntervalExpUpper_auto2513
    (sigma x : ℝ) (t a coefficientBound upper : Fin 30 → ℝ)
    (hinside : ∀ i : Fin 30, |x| < ownerRad_2463 i)
    (ht : ∀ i : Fin 30, 0 ≤ t i)
    (htone : ∀ i : Fin 30, t i < 1)
    (hcoord : ∀ i : Fin 30, |x / ownerRad_2463 i| ≤ t i)
    (ha : ∀ i : Fin 30, 0 ≤ a i)
    (haone : ∀ i : Fin 30, a i < 1)
    (halower : ∀ i : Fin 30, a i ≤ |x / ownerRad_2463 i|)
    (hcoefficient : ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound i)
    (hupper : ∀ i : Fin 30,
      Real.exp (-30 / (1 - (a i) ^ 2)) ≤ upper i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
        (coefficientBound i * upper i)
        (coefficientBound i * upper i *
          (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
            |ownerMod_2463 i|))
        (coefficientBound i * upper i *
          ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
              4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
              (ownerRad_2463 i) ^ 2) +
            (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i) ^ 2 +
            (ownerMod_2463 i) ^ 2 +
            2 * |ownerMod_2463 i| *
              (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i))) := by
  apply ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
  intro i
  exact weightedExternalFamilySecondDeriv_le_of_interval_exp_upper_auto2513
    sigma x (ownerMod_2463 i) (ownerRad_2463 i) (t i) (a i)
    (coefficientBound i) (upper i) (ownerCoef_2463 i)
    (ownerRadPos_2465 i) (hinside i) (ht i) (htone i) (hcoord i)
    (ha i) (haone i) (halower i) (hcoefficient i) (hupper i)

theorem ownerPanelWeightedSecondDeriv_le_sumIntervalExpUpperOrZero_auto2513
    (sigma x : ℝ) (t a coefficientBound upper : Fin 30 → ℝ)
    (hdata : ∀ i : Fin 30, |x| < ownerRad_2463 i →
      0 ≤ t i ∧ t i < 1 ∧ |x / ownerRad_2463 i| ≤ t i ∧
      0 ≤ a i ∧ a i < 1 ∧ a i ≤ |x / ownerRad_2463 i|)
    (hcoefficient : ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound i)
    (hupper : ∀ i : Fin 30, |x| < ownerRad_2463 i →
      Real.exp (-30 / (1 - (a i) ^ 2)) ≤ upper i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, if ownerRad_2463 i ≤ |x| then 0 else
        weightedCurvature2348 sigma (ownerRad_2463 i)
          (coefficientBound i * upper i)
          (coefficientBound i * upper i *
            (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
              |ownerMod_2463 i|))
          (coefficientBound i * upper i *
            ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
                4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
                (ownerRad_2463 i) ^ 2) +
              (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i) ^ 2 +
              (ownerMod_2463 i) ^ 2 +
              2 * |ownerMod_2463 i| *
                (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i))) := by
  apply ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
  intro i
  by_cases houtside : ownerRad_2463 i ≤ |x|
  · rw [if_pos houtside]
    rw [weightedExternalFamilySecondDeriv_zero_of_outside2488 sigma
      (ownerCoef_2463 i) (ownerMod_2463 i) (ownerRad_2463 i) x
      (ownerRadPos_2465 i) houtside]
    simp
  · rw [if_neg houtside]
    have hinside : |x| < ownerRad_2463 i := lt_of_not_ge houtside
    rcases hdata i hinside with ⟨ht, htone, hcoord, ha, haone, halower⟩
    exact weightedExternalFamilySecondDeriv_le_of_interval_exp_upper_auto2513
      sigma x (ownerMod_2463 i) (ownerRad_2463 i) (t i) (a i)
      (coefficientBound i) (upper i) (ownerCoef_2463 i)
      (ownerRadPos_2465 i) hinside ht htone hcoord ha haone halower
      (hcoefficient i) (hupper i hinside)

end ConnesWeilRH.Dev
