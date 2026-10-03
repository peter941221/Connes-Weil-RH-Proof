import ConnesWeilRH.Dev.C1RouteAExpProductionTable2519

/-! 2520: formal control of the archimedean weight used by the cell term.

The table payload does not prove its own cell inequalities.  This lemma
isolates one missing analytic factor for the actual producer rows
`sigma = ± 1/2` and bounds it by a rational constant using Mathlib's Taylor
remainder bound for `Real.exp`.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

set_option linter.style.longLine false

theorem ownerExpWeight_le_64_2520
    {sigma : ℝ} (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ)) :
    Real.exp (|sigma| * stripRadius2303) ≤ 64 := by
  have harg : 0 ≤ |sigma| * stripRadius2303 := by
    exact mul_nonneg (abs_nonneg sigma) (by norm_num [stripRadius2303])
  have harg' : |sigma| * stripRadius2303 ≤ (33 / 4 : ℝ) / 2 := by
    rcases hsigma with rfl | rfl <;> norm_num [stripRadius2303, abs_of_nonneg,
      abs_of_nonpos]
  have harg5 : |( |sigma| * stripRadius2303) / 5| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (div_nonneg harg (by norm_num))]
    linarith
  have h := Real.exp_bound (x := (|sigma| * stripRadius2303) / 5)
    harg5 (n := 20) (by norm_num)
  have hupp := (abs_sub_le_iff.mp h).1
  have hseries : Real.exp ((|sigma| * stripRadius2303) / 5) ≤
      (∑ m ∈ Finset.range 20,
        ((|sigma| * stripRadius2303) / 5) ^ m / (m.factorial : ℝ)) +
        ((|sigma| * stripRadius2303) / 5) ^ 20 *
          ((↑(Nat.succ 20) : ℝ) / ((Nat.factorial 20 : ℝ) * 20)) := by
    rw [abs_of_nonneg (div_nonneg harg (by norm_num))] at hupp
    linarith
  have hscaled : Real.exp ((|sigma| * stripRadius2303) / 5) ≤
      (229 / 100 : ℝ) := by
    calc
      Real.exp ((|sigma| * stripRadius2303) / 5) ≤ _ := hseries
      _ ≤
          (∑ m ∈ Finset.range 20,
            ((33 / 4 : ℝ) / 2 / 5) ^ m / (m.factorial : ℝ)) +
            ((33 / 4 : ℝ) / 2 / 5) ^ 20 *
              ((↑(Nat.succ 20) : ℝ) /
                ((Nat.factorial 20 : ℝ) * 20)) := by
        gcongr
      _ ≤ (229 / 100 : ℝ) := by norm_num [Finset.sum_range_succ]
  calc
    Real.exp (|sigma| * stripRadius2303) =
        (Real.exp ((|sigma| * stripRadius2303) / 5)) ^ 5 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (229 / 100 : ℝ) ^ 5 := by gcongr
    _ ≤ 64 := by norm_num

end ConnesWeilRH.Dev
