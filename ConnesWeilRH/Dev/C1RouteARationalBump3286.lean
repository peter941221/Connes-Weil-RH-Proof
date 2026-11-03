import ConnesWeilRH.Dev.C1RouteARationalBump3285

namespace ConnesWeilRH.Dev

def ratBumpT3286 (radius position : ℚ) : ℚ :=
  30 - 30 / (1 - (position / radius) ^ 2)

def ratBumpInterval3286 (t : ℚ) : RatInterval3276 :=
  if |t / 8| ≤ (1 : ℚ) then
    ratCentralBumpInterval3284 t
  else
    ratTailBumpInterval3285

theorem ratBumpInterval_mem3286
    {radius position t : ℚ}
    (hradius : 0 < (radius : ℝ))
    (hposition : 0 ≤ (position : ℝ))
    (hinside : (position : ℝ) < radius)
    (ht : (t : ℝ) = 30 - 30 / (1 - ((position : ℝ) / radius) ^ 2))
    (htnonpos : (t : ℝ) ≤ 0) :
    (ratBumpInterval3286 t).Mem
      (C1RouteAOwnerScaleAudit.widthBump (radius : ℝ) (position : ℝ)) := by
  by_cases hsmall : |t / 8| ≤ (1 : ℚ)
  · simp only [ratBumpInterval3286, if_pos hsmall]
    apply ratCentralBumpInterval_mem3284 hradius hposition hinside ht
    exact_mod_cast hsmall
  · simp only [ratBumpInterval3286, if_neg hsmall]
    apply ratTailBumpInterval_mem3285 hradius hposition hinside
    · have hnot : ¬ |((t / 8 : ℚ) : ℝ)| ≤ 1 := by
        intro hreal
        apply hsmall
        exact_mod_cast hreal
      have hcast : ((t / 8 : ℚ) : ℝ) = (t : ℝ) / 8 := by norm_num
      rw [hcast] at hnot
      have habs : 1 < |(t : ℝ) / 8| := lt_of_not_ge hnot
      have hneg : (t : ℝ) / 8 < -1 := by
        by_cases hnonneg : 0 ≤ (t : ℝ) / 8
        · rw [abs_of_nonneg hnonneg] at habs
          linarith
        · have hnonpos : (t : ℝ) / 8 ≤ 0 := le_of_not_ge hnonneg
          rw [abs_of_nonpos hnonpos] at habs
          linarith
      have ht8 : (t : ℝ) < -8 := by
        nlinarith [hneg]
      exact le_of_lt ht8
    · exact ht

end ConnesWeilRH.Dev