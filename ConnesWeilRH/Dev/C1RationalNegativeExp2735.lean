import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificate

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

theorem rational_negative_exp_box2735 {w : ℝ} (hw : 0 ≤ w) (m : ℕ)
    (hm : 1 ≤ m) (hwm : w ≤ m) :
    ((expTaylor (w / m) + expTail (w / m)) ^ m)⁻¹ ≤ Real.exp (-w) ∧
      Real.exp (-w) ≤ ((expTaylor (w / m) - expTail (w / m)) ^ m)⁻¹ := by
  have h := exp_bounds_pow (w := w) hw hm hwm
  have hp : 0 < expTaylor (w / m) - expTail (w / m) := by
    have hy0 : 0 ≤ w / m := by positivity
    have hy1 : w / m ≤ 1 := by
      exact (div_le_one (by positivity)).mpr hwm
    exact lt_of_lt_of_le zero_lt_one (one_le_expTaylor_sub_expTail hy0 hy1)
  have hq : 0 < expTaylor (w / m) + expTail (w / m) := by
    have hy0 : 0 ≤ w / m := by positivity
    have ht := one_le_expTaylor hy0
    have hr : 0 ≤ expTail (w / m) := by unfold expTail; positivity
    linarith
  rw [Real.exp_neg]
  constructor
  · simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos w) h.2
  · simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hp m) h.1

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
