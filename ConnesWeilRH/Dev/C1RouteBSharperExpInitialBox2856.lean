import ConnesWeilRH.Dev.C1RouteBExpInitialBox2849
import ConnesWeilRH.Dev.C1SeedIntervalJet2734

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

lemma exp_neg_one_lower2855 : (9 / 25 : ℝ) < Real.exp (-1) := by
  have h := Real.exp_bound (x := (-1 : ℝ)) (by norm_num) (n := 30) (by norm_num)
  have hlo := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ] at hlo
  nlinarith

lemma exp_neg_two_thirds_lower2855 : (1 / 2 : ℝ) < Real.exp (-(2 / 3 : ℝ)) := by
  have h := Real.exp_bound (x := (-(2 / 3 : ℝ))) (by norm_num) (n := 30) (by norm_num)
  have hlo := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ] at hlo
  nlinarith

lemma exp_neg_one_upper2855 : Real.exp (-1) < (3 / 8 : ℝ) := by
  have h := Real.exp_bound (x := (-1 : ℝ)) (by norm_num) (n := 30) (by norm_num)
  have hup := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hup
  nlinarith

lemma exp_neg_three_fifths_upper2855 :
    Real.exp (-(3 / 5 : ℝ)) < (3 / 5 : ℝ) := by
  have h := Real.exp_bound (x := (-(3 / 5 : ℝ))) (by norm_num) (n := 30) (by norm_num)
  have hup := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hup
  nlinarith

lemma exp_neg_eight_thirds_lower_split2855 :
    (1 / 16 : ℝ) < Real.exp (-(8 / 3 : ℝ)) := by
  rw [show (-(8 / 3 : ℝ)) = (-1 : ℝ) + (-1 : ℝ) + (-(2 / 3 : ℝ)) by ring,
    Real.exp_add, Real.exp_add]
  have h1 := exp_neg_one_lower2855
  have h2 := exp_neg_two_thirds_lower2855
  calc
    (1 / 16 : ℝ) < (9 / 25 : ℝ) * (9 / 25 : ℝ) * (1 / 2 : ℝ) := by norm_num
    _ < Real.exp (-1) * Real.exp (-1) * Real.exp (-(2 / 3 : ℝ)) := by
      have hsq : (9 / 25 : ℝ) * (9 / 25 : ℝ) <
          Real.exp (-1) * Real.exp (-1) := by
        calc
          (9 / 25 : ℝ) * (9 / 25 : ℝ) < (9 / 25 : ℝ) * Real.exp (-1) :=
            mul_lt_mul_of_pos_left h1 (by norm_num)
          _ < Real.exp (-1) * Real.exp (-1) :=
            mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      calc
        (9 / 25 : ℝ) * (9 / 25 : ℝ) * (1 / 2 : ℝ) <
            (Real.exp (-1) * Real.exp (-1)) * (1 / 2 : ℝ) :=
          mul_lt_mul_of_pos_right hsq (by norm_num)
        _ < (Real.exp (-1) * Real.exp (-1)) * Real.exp (-(2 / 3 : ℝ)) :=
          mul_lt_mul_of_pos_left h2 (by positivity)

lemma exp_neg_thirteen_fifths_upper_split2855 :
    Real.exp (-(13 / 5 : ℝ)) < (1 / 8 : ℝ) := by
  rw [show (-(13 / 5 : ℝ)) = (-1 : ℝ) + (-1 : ℝ) + (-(3 / 5 : ℝ)) by ring,
    Real.exp_add, Real.exp_add]
  have h1 := exp_neg_one_upper2855
  have h2 := exp_neg_three_fifths_upper2855
  calc
    Real.exp (-1) * Real.exp (-1) * Real.exp (-(3 / 5 : ℝ)) <
        (3 / 8 : ℝ) * (3 / 8 : ℝ) * (3 / 5 : ℝ) := by
      have hsq : Real.exp (-1) * Real.exp (-1) <
          (3 / 8 : ℝ) * (3 / 8 : ℝ) := by
        calc
          Real.exp (-1) * Real.exp (-1) < (3 / 8 : ℝ) * Real.exp (-1) :=
            mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
          _ < (3 / 8 : ℝ) * (3 / 8 : ℝ) :=
            mul_lt_mul_of_pos_left h1 (by norm_num)
      exact mul_lt_mul hsq (le_of_lt h2) (by positivity) (by positivity)
    _ < (1 / 8 : ℝ) := by norm_num

def routeBSharperExpBox2856 : RationalBox2744 :=
  { lo := 1 / 16, hi := 1 / 8, ordered := by norm_num }

theorem routeB_sharper_exp_initial_box_mem2856 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    routeBSharperExpBox2856.Mem (transitionExp2731 x) := by
  have hlo : 0 < routeBCell4096Interval2845.lo := by
    norm_num [routeBCell4096Interval2845]
  have hhi : routeBCell4096Interval2845.hi < 1 := by
    norm_num [routeBCell4096Interval2845]
  have hp := phaseJetInterval_mem2734 routeBCell4096Interval2845 0 hlo hhi hx
  have hc := routeB_phase_box_contains_lean_interval2845 0 (by norm_num)
  have hp' : (routeBPhase2844 0).Mem (transitionPhase2731 x) :=
    ⟨le_trans hc.1 hp.1, le_trans hp.2 hc.2⟩
  have hlow : (-(8 / 3 : ℝ)) ≤ transitionPhase2731 x := by
    exact le_trans (by norm_num [routeBPhase2844]) hp'.1
  have hupp : transitionPhase2731 x ≤ (-(13 / 5 : ℝ)) := by
    exact le_trans hp'.2 (by norm_num [routeBPhase2844])
  simp only [routeBSharperExpBox2856, RationalBox2744.Mem, transitionExp2731]
  constructor
  · convert (le_of_lt exp_neg_eight_thirds_lower_split2855).trans
      (Real.exp_le_exp.mpr hlow) using 1 <;> norm_num
  · convert (Real.exp_le_exp.mpr hupp).trans
      (le_of_lt exp_neg_thirteen_fifths_upper_split2855) using 1 <;> norm_num

end
end ConnesWeilRH.Dev

