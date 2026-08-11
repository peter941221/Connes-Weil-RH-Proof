import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Exp

/-! probe -/
open scoped Topology

lemma expOneLt : Real.exp 1 < (11/4 : ℝ) := by
  have h := Real.exp_bound' (x := (1:ℝ)) (by norm_num) (by norm_num) (n := 7) (hn := by norm_num)
  norm_num [Finset.sum_range_succ] at h
  have hlt : (1957 / 720 + 1 / 4410 : ℝ) < 11/4 := by norm_num
  nlinarith

lemma expTwo_lt : Real.exp 2 < (121/16 : ℝ) := by
  have h := expOneLt
  calc
    Real.exp 2 = Real.exp (1 + 1) := by norm_num
    _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
    _ < (11/4) * (11/4) := by nlinarith [h, Real.exp_pos (1:ℝ)]
    _ = (121/16:ℝ) := by norm_num

lemma expTwoFifths_lt : Real.exp (2/5) < (3/2 : ℝ) := by
  have h := Real.exp_bound' (x := (2/5:ℝ)) (by norm_num) (by norm_num) (n := 7) (hn := by norm_num)
  have hle : (∑ m ∈ Finset.range 7, (2/5:ℝ)^m / m.factorial) +
      (2/5:ℝ)^7 * (7+1) / (Nat.factorial 7 * 7) < (3/2:ℝ) := by
    norm_num [Finset.sum_range_succ]
  nlinarith

lemma expTwelveFifths_lt : Real.exp (12/5) < (12 : ℝ) := by
  calc
    Real.exp (12/5) = Real.exp (2 + 2/5) := by norm_num
    _ = Real.exp 2 * Real.exp (2/5) := by rw [Real.exp_add]
    _ < (121/16) * (3/2) := by
      nlinarith [expTwo_lt, expTwoFifths_lt, Real.exp_pos (2:ℝ), Real.exp_pos (2/5:ℝ)]
    _ = (363/32:ℝ) := by norm_num
    _ < 12 := by norm_num

lemma expTwelveFifths_lt_fourPi : Real.exp (12/5) < 4 * Real.pi := by
  have h1 : Real.exp (12/5) < (12 : ℝ) := expTwelveFifths_lt
  have h2 : (12 : ℝ) < 4 * Real.pi := by
    have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  exact lt_trans h1 h2

lemma logFourPi_gt : (12/5 : ℝ) < Real.log (4 * Real.pi) := by
  have hpos : 0 < Real.exp (12/5) := Real.exp_pos _
  have hlt := expTwelveFifths_lt_fourPi
  have hlog : Real.log (Real.exp (12/5)) < Real.log (4 * Real.pi) :=
    Real.log_lt_log hpos hlt
  simpa [Real.log_exp] using hlog

lemma archCoeff_gt : (29/10 : ℝ) <
    Real.log (4 * Real.pi) + Real.eulerMascheroniConstant := by
  have hlog : (12/5 : ℝ) < Real.log (4 * Real.pi) := logFourPi_gt
  have hgam : (1/2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  linarith
