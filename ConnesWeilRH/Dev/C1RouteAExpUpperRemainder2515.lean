import ConnesWeilRH.Dev.C1RouteAExpIntervalUpper2512

/-! Record 2515: expose the certified exponential upper at the remainder-ladder
interface.  The unsafe branch remains the existing L1 fallback.
-/

namespace ConnesWeilRH.Dev

noncomputable def ownerExpUpperCurvatureSum2515
    (sigma : ℝ) (t coefficientBound upper : ℕ → Fin 30 → ℝ)
    (index : ℕ) : ℝ :=
  ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
    (coefficientBound index i * upper index i)
    (coefficientBound index i * upper index i *
      (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
        ownerRad_2463 i + |ownerMod_2463 i|))
    (coefficientBound index i * upper index i *
      ((60 * ((1 - (t index i) ^ 2)⁻¹ ^ 2 +
          4 * (t index i) ^ 2 * (1 - (t index i) ^ 2)⁻¹ ^ 3) /
          (ownerRad_2463 i) ^ 2) +
        (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
          ownerRad_2463 i) ^ 2 + (ownerMod_2463 i) ^ 2 +
        2 * |ownerMod_2463 i| *
          (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
            ownerRad_2463 i)))

theorem ownerPanelStripNorm_le_expUpperCurvature2515
    (sigma radius step : ℝ) (cells : ℕ)
    (safe : ℕ → Bool)
    (t a coefficientBound upper : ℕ → Fin 30 → ℝ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hsafeInside : ∀ index ∈ Finset.range cells, safe index = true →
      ∀ coordinate ∈ Set.Icc (-radius + index * step)
        (-radius + (index + 1) * step),
        ∀ i : Fin 30, |coordinate| < ownerRad_2463 i)
    (ht : ∀ index ∈ Finset.range cells, safe index = true → ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, 0 ≤ t index i)
    (htone : ∀ index ∈ Finset.range cells, safe index = true → ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, t index i < 1)
    (hcoord : ∀ index ∈ Finset.range cells, safe index = true → ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate / ownerRad_2463 i| ≤ t index i)
    (ha : ∀ index ∈ Finset.range cells, safe index = true → ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, 0 ≤ a index i)
    (haone : ∀ index ∈ Finset.range cells, safe index = true → ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, a index i < 1)
    (halower : ∀ index ∈ Finset.range cells, safe index = true → ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, a index i ≤ |coordinate / ownerRad_2463 i|)
    (hcoefficient : ∀ index ∈ Finset.range cells, ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound index i)
    (hupper : ∀ index ∈ Finset.range cells, safe index = true →
      ∀ i : Fin 30, Real.exp (-30 / (1 - (a index i) ^ 2)) ≤ upper index i) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
      localCurvatureRemainder2474
        (fun index => if safe index = true then
          ownerExpUpperCurvatureSum2515 sigma t coefficientBound upper index
        else ownerWeightedCurvatureL1_2480 sigma radius) step cells := by
  apply ownerPanelStripNorm_le_localCurvature2475 sigma radius step cells
    (fun index => if safe index = true then
      ownerExpUpperCurvatureSum2515 sigma t coefficientBound upper index
    else ownerWeightedCurvatureL1_2480 sigma radius) hradius hR hstep hgrid
  intro index hindex coordinate hcoordinate
  by_cases hsafe : safe index = true
  · rw [if_pos hsafe]
    unfold ownerExpUpperCurvatureSum2515
    apply ownerPanelWeightedSecondDeriv_le_sumIntervalExpUpper_auto2513
      sigma coordinate (t index) (a index) (coefficientBound index)
      (upper index)
    · exact hsafeInside index hindex hsafe coordinate hcoordinate
    · exact ht index hindex hsafe coordinate hcoordinate
    · exact htone index hindex hsafe coordinate hcoordinate
    · exact hcoord index hindex hsafe coordinate hcoordinate
    · exact ha index hindex hsafe coordinate hcoordinate
    · exact haone index hindex hsafe coordinate hcoordinate
    · exact halower index hindex hsafe coordinate hcoordinate
    · exact hcoefficient index hindex
    · exact hupper index hindex hsafe
  · rw [if_neg hsafe]
    apply ownerPanelWeightedSecondDerivBoundL1_2480 sigma radius coordinate
    have hleft : -radius + (index : ℝ) * step ≤ coordinate := hcoordinate.1
    have hright : coordinate ≤ -radius + ((index + 1 : ℕ) : ℝ) * step := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcoordinate.2
    have hindexnonneg : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
    have hstepnonneg : 0 ≤ step := hstep.le
    have hindexsucc : (index : ℝ) + 1 ≤ (cells : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hindex)
    have hindexstep : ((index : ℝ) + 1) * step ≤ (cells : ℝ) * step :=
      mul_le_mul_of_nonneg_right hindexsucc hstepnonneg
    apply abs_le.mpr
    constructor
    · have hidxprod : 0 ≤ (index : ℝ) * step :=
        mul_nonneg hindexnonneg hstepnonneg
      linarith
    · calc
        coordinate ≤ -radius + ((index : ℝ) + 1) * step := by
          simpa only [Nat.cast_add, Nat.cast_one] using hright
        _ ≤ -radius + (cells : ℝ) * step := by linarith
        _ = radius := by rw [hgrid]; ring

end ConnesWeilRH.Dev
