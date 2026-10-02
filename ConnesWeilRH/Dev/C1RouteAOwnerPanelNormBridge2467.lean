import ConnesWeilRH.Dev.C1RouteAOwnerIndexedPanel2466
import ConnesWeilRH.Dev.C1RouteANormBridge2453

/-  2467: norm-facing consumer of the universal panel rectangle.

This is the immediate bridge from the indexed owner envelope to the scalar
strip integrand: rectangle containment is converted to a complex-norm bound,
and then to the nonnegative exponential-weighted form used by stripNorm. -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

noncomputable def ownerPanelSumValue_2467 (x : ℝ) : ℂ :=
  ∑ i : Fin 30,
    externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
      (ownerRad_2463 i) x

noncomputable def ownerPanelNormBox_2467 (x0 x1 : ℝ) : ℝ :=
  max |(ComplexRect2427.sumFinset (ownerPanelRect_2466 x0 x1) Finset.univ).reLo|
      |(ComplexRect2427.sumFinset (ownerPanelRect_2466 x0 x1) Finset.univ).reHi| +
  max |(ComplexRect2427.sumFinset (ownerPanelRect_2466 x0 x1) Finset.univ).imLo|
      |(ComplexRect2427.sumFinset (ownerPanelRect_2466 x0 x1) Finset.univ).imHi|

theorem ownerPanelNormBound_2467 {x0 x1 x : ℝ}
    (h01 : x0 ≤ x1) (hx : x ∈ Set.Icc x0 x1) :
    ‖ownerPanelSumValue_2467 x‖ ≤ ownerPanelNormBox_2467 x0 x1 := by
  exact norm_le_of_rect_mem_2453 _ (ownerPanelMem_2466 h01 x hx)

theorem ownerPanelWeightedNormBound_2467 {x0 x1 x σ : ℝ}
    (h01 : x0 ≤ x1) (hx : x ∈ Set.Icc x0 x1) :
    Real.exp (σ * x) * ‖ownerPanelSumValue_2467 x‖ ≤
      Real.exp (σ * x) * ownerPanelNormBox_2467 x0 x1 := by
  exact mul_le_mul_of_nonneg_left (ownerPanelNormBound_2467 h01 hx)
    (le_of_lt (Real.exp_pos _))

end ConnesWeilRH.Dev
