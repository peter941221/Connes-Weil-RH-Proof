import ConnesWeilRH.Dev.C1RouteAOwnerWeightedFamily2488

/-! Record 2501: the lower endpoint ratio for the exponential envelope.

The derivative factors use the maximum endpoint ratio.  The negative
exponential is monotone in the opposite direction, so its cellwise lower
ratio is zero on a cell crossing zero and the nearer endpoint on a same-sign
cell.  This file proves only that geometric interface; it does not yet bind
the rational 2501 payload or close an hcell.
-/

namespace ConnesWeilRH.Dev

noncomputable def ownerCellLowerRatio2501
    (radius step : ℝ) (index : ℕ) (i : Fin 30) : ℝ :=
  if (-radius + index * step ≤ 0 ∧
      0 ≤ -radius + (index + 1) * step) then 0 else
    min |(-radius + index * step)|
      |(-radius + (index + 1) * step)| / ownerRad_2463 i

theorem min_abs_endpoints_le_abs_of_mem_Icc2501
    {left right coordinate : ℝ}
    (horder : left ≤ right) (hcoordinate : coordinate ∈ Set.Icc left right)
    (hcroses : ¬ (left ≤ 0 ∧ 0 ≤ right)) :
    min |left| |right| ≤ |coordinate| := by
  by_cases hright : right < 0
  · have hleft : left < 0 := lt_of_le_of_lt horder hright
    rw [abs_of_neg hleft, abs_of_neg hright, abs_of_neg]
    · exact min_le_iff.mpr (Or.inr (by linarith [hcoordinate.2]))
    · linarith [hcoordinate.2, hright]
  · have hright0 : 0 ≤ right := le_of_not_gt hright
    have hleft : 0 < left := by
      by_contra hleft
      have : left ≤ 0 := le_of_not_gt hleft
      exact hcroses ⟨this, hright0⟩
    rw [abs_of_pos hleft, abs_of_nonneg hright0, abs_of_nonneg]
    · exact min_le_iff.mpr (Or.inl (by linarith [hcoordinate.1]))
    · linarith [hcoordinate.1, hleft]

theorem ownerCellLowerRatio_le_normalizedAbs2501
    {radius step coordinate : ℝ} {index : ℕ} (i : Fin 30)
    (hradius : 0 < ownerRad_2463 i) (hstep : 0 ≤ step)
    (hcoordinate : coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step)) :
    ownerCellLowerRatio2501 radius step index i ≤
      |coordinate / ownerRad_2463 i| := by
  let left : ℝ := -radius + index * step
  let right : ℝ := -radius + (index + 1) * step
  have horder : left ≤ right := by
    dsimp [left, right]
    have hnat : (0 : ℝ) ≤ index := by positivity
    nlinarith
  have hcoordinate' : coordinate ∈ Set.Icc left right := by
    simpa [left, right] using hcoordinate
  by_cases hcroses : left ≤ 0 ∧ 0 ≤ right
  · simp [ownerCellLowerRatio2501, left, right, hcroses]
  · rw [show ownerCellLowerRatio2501 radius step index i =
      min |left| |right| / ownerRad_2463 i by
        have hnot : ¬ (-radius + (index : ℝ) * step ≤ 0 ∧
            0 ≤ -radius + ((index : ℝ) + 1) * step) := by
          intro hbad
          apply hcroses
          simpa [left, right] using hbad
        unfold ownerCellLowerRatio2501
        rw [if_neg hnot]]
    rw [abs_div]
    rw [abs_of_pos hradius]
    apply (div_le_div_iff_of_pos_right hradius).2
    exact min_abs_endpoints_le_abs_of_mem_Icc2501 horder hcoordinate' hcroses

theorem ownerCellLowerRatio_nonneg2501
    (radius step : ℝ) (index : ℕ) (i : Fin 30) :
    0 ≤ ownerCellLowerRatio2501 radius step index i := by
  unfold ownerCellLowerRatio2501
  split
  · norm_num
  · exact div_nonneg
      (le_min (abs_nonneg _) (abs_nonneg _))
      (ownerRadPos_2465 i).le

end ConnesWeilRH.Dev
