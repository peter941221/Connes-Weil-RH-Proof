import ConnesWeilRH.Dev.C1RouteACompactExp2542

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def bumpMultiplier2543 (order : ℕ) (radius position : ℝ) : ℝ :=
  (bumpDeficit2350 (position / radius))⁻¹ ^ (2 * order) *
    bumpNumerator2350 order (position / radius) / radius ^ order

noncomputable def weightedMultiplier2543 (order : ℕ)
    (sigma modulation radius position : ℝ) : ℂ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℂ) *
    weightedLambda2537 sigma modulation ^ index *
    (bumpMultiplier2543 (order - index) radius position : ℂ)

theorem widthBump_inside_factor2543 (order : ℕ) (horder : order ≤ 4)
    {radius position : ℝ} (hradius : 0 < radius) (hx : |position| < radius) :
    iteratedDeriv order (widthBump radius) position =
      bumpMultiplier2543 order radius position * widthBump radius position := by
  rw [widthBump_iteratedDeriv_inside2350 order horder hradius hx]
  simp only [scaledBumpJet2350, bumpJet2350, bumpMultiplier2543,
    widthBump, if_pos hx, bumpDeficit2350]
  ring

theorem weightedFamily_inside_factor2543 (order : ℕ) (horder : order ≤ 4)
    (sigma modulation : ℝ) {radius position : ℝ}
    (hradius : 0 < radius) (hx : |position| < radius) :
    iteratedDeriv order
      (weightedFunction2348 sigma (externalFamilyValue2344 1 modulation radius)) position =
      weightedMultiplier2543 order sigma modulation radius position *
        weightedFunction2348 sigma (externalFamilyValue2344 1 modulation radius) position := by
  rw [weightedExternalFamily_iteratedDeriv2537 order sigma 1 modulation hradius]
  simp only [one_mul]
  rw [weightedExternalFamily_eq2537]
  simp only [one_mul, weightedMultiplier2543, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  rw [weightedPhase2537_iteratedDeriv,
    widthBump_inside_factor2543 (order-index) (by omega) hradius hx]
  push_cast
  ring

theorem weightedFamily_outside_zero2543 (order : ℕ) (sigma modulation : ℝ)
    {radius position : ℝ} (hradius : 0 < radius) (hx : radius ≤ |position|) :
    iteratedDeriv order
      (weightedFunction2348 sigma (externalFamilyValue2344 1 modulation radius)) position = 0 := by
  rw [weightedExternalFamily_iteratedDeriv2537 order sigma 1 modulation hradius]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro index _
  rw [widthBump_iteratedDeriv_outside2350 (order-index) hradius hx]
  simp

theorem complex_multiplier_error2543 (multiplier value center : ℂ) (error magnitude : ℝ)
    (herror : ‖value - center‖ ≤ error) (hmagnitude : ‖multiplier‖ ≤ magnitude) :
    ‖multiplier * value - multiplier * center‖ ≤ magnitude * error := by
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left herror (norm_nonneg multiplier)).trans
    (mul_le_mul_of_nonneg_right hmagnitude ((norm_nonneg _).trans herror))

end ConnesWeilRH.Dev
