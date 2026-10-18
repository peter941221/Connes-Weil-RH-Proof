import ConnesWeilRH.Dev.C1RouteBPhaseBoxBridge2845

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def routeBExpInitialBox2849 : RationalBox2744 :=
  { lo := 1 / 32, hi := 1 / 4, ordered := by norm_num }

lemma exp_neg_one_lower_InitialBox2849 :
    (1 / 3 : ℝ) < Real.exp (-1) := by
  have h := Real.exp_bound (x := (-1 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have hlo := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ] at hlo
  nlinarith

lemma exp_neg_one_upper_InitialBox2849 :
    Real.exp (-1) < (3 / 8 : ℝ) := by
  have h := Real.exp_bound (x := (-1 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have hup := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hup
  nlinarith

lemma exp_neg_three_lower_InitialBox2849 :
    (1 / 32 : ℝ) < Real.exp (-3) := by
  rw [show (-3 : ℝ) = (-1 : ℝ) + (-1 : ℝ) + (-1 : ℝ) by norm_num,
    Real.exp_add, Real.exp_add]
  nlinarith [exp_neg_one_lower_InitialBox2849]

lemma exp_neg_two_upper_InitialBox2849 :
    Real.exp (-2) < (1 / 4 : ℝ) := by
  rw [show (-2 : ℝ) = (-1 : ℝ) + (-1 : ℝ) by norm_num, Real.exp_add]
  calc
    Real.exp (-1) * Real.exp (-1) < (3 / 8 : ℝ) * Real.exp (-1) :=
      mul_lt_mul_of_pos_right exp_neg_one_upper_InitialBox2849 (Real.exp_pos _)
    _ < (3 / 8 : ℝ) * (3 / 8 : ℝ) :=
      mul_lt_mul_of_pos_left exp_neg_one_upper_InitialBox2849 (by norm_num)
    _ < (1 / 4 : ℝ) := by norm_num

theorem routeB_exp_initial_box_mem2849 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    routeBExpInitialBox2849.Mem (transitionExp2731 x) := by
  have hlo : 0 < routeBCell4096Interval2845.lo := by
    norm_num [routeBCell4096Interval2845]
  have hhi : routeBCell4096Interval2845.hi < 1 := by
    norm_num [routeBCell4096Interval2845]
  have hp := phaseJetInterval_mem2734 routeBCell4096Interval2845 0 hlo hhi hx
  have hc := routeB_phase_box_contains_lean_interval2845 0 (by norm_num)
  have hp' : (routeBPhase2844 0).Mem (transitionPhase2731 x) :=
    ⟨le_trans hc.1 hp.1, le_trans hp.2 hc.2⟩
  have hlow : (-3 : ℝ) ≤ transitionPhase2731 x := by
    exact le_trans (by norm_num [routeBPhase2844]) hp'.1
  have hupp : transitionPhase2731 x ≤ (-2 : ℝ) := by
    exact le_trans hp'.2 (by norm_num [routeBPhase2844])
  simp only [routeBExpInitialBox2849, RationalBox2744.Mem,
    transitionExp2731]
  constructor
  · convert (le_of_lt exp_neg_three_lower_InitialBox2849).trans
      (Real.exp_le_exp.mpr hlow) using 1 <;> norm_num
  · convert (Real.exp_le_exp.mpr hupp).trans
      (le_of_lt exp_neg_two_upper_InitialBox2849) using 1 <;> norm_num

end
end ConnesWeilRH.Dev
