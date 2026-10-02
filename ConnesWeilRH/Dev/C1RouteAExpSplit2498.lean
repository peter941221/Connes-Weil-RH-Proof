import ConnesWeilRH.Dev.C1ScaledExpRationalEnvelope

/-! Record 2498: a reusable rational envelope for negative exponentials.

The owner-cell exponents are negative and often much larger than one in
absolute value.  This lemma splits `z = n + r`, with `r ∈ [0,1]`, so the
existing unit-interval Taylor enclosure handles the remainder and a fixed
rational upper bound handles the integer part.  It is an analytic interface;
no owner-cell payload is imported here.
-/

namespace ConnesWeilRH.Source.C1ScaledExpRationalEnvelope

noncomputable section

def expNegOneUpper2498 : ℝ :=
  (3678794411714424 : ℝ) / 10000000000000000

theorem exp_neg_one_le_expNegOneUpper2498 :
    Real.exp (-1 : ℝ) ≤ expNegOneUpper2498 := by
  have h := Real.exp_bound (x := (-1 : ℝ)) (by norm_num)
    (n := 20) (by norm_num)
  have hu := (abs_le.mp h).2
  norm_num [expNegOneUpper2498, Finset.sum_range_succ] at hu ⊢
  linarith

theorem exp_neg_split_upper2498 (n : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.exp (-((n : ℝ) + r)) ≤
      expNegOneUpper2498 ^ n *
        (expTaylor20 r + expTaylor20Error) := by
  have hunit := expTaylor20_error r hr0 hr1
  have hunit_upper : Real.exp (-r) ≤ expTaylor20 r + expTaylor20Error := by
    have habs := (abs_le.mp hunit).2
    calc
      Real.exp (-r) = (Real.exp (-r) - expTaylor20 r) + expTaylor20 r := by ring
      _ ≤ expTaylor20 r + expTaylor20Error := by linarith
  have hpow : Real.exp (-1 : ℝ) ^ n ≤ expNegOneUpper2498 ^ n := by
    exact pow_le_pow_left₀ (Real.exp_pos (-1)).le
      exp_neg_one_le_expNegOneUpper2498 n
  have hpow_nonneg : 0 ≤ Real.exp (-1 : ℝ) ^ n := by positivity
  have hunit_nonneg : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have hupper_nonneg : 0 ≤ expNegOneUpper2498 ^ n := by
    exact pow_nonneg (by norm_num [expNegOneUpper2498]) n
  have hfactor :
      Real.exp (-1 : ℝ) ^ n * Real.exp (-r) ≤
        expNegOneUpper2498 ^ n * (expTaylor20 r + expTaylor20Error) := by
    calc
      Real.exp (-1 : ℝ) ^ n * Real.exp (-r) ≤
          expNegOneUpper2498 ^ n * Real.exp (-r) :=
        mul_le_mul_of_nonneg_right hpow hunit_nonneg
      _ ≤ expNegOneUpper2498 ^ n *
          (expTaylor20 r + expTaylor20Error) := by
        exact mul_le_mul_of_nonneg_left hunit_upper hupper_nonneg
  calc
    Real.exp (-((n : ℝ) + r)) =
        Real.exp (-((n : ℝ)) + (-r)) := by ring_nf
    _ = Real.exp (-((n : ℝ))) * Real.exp (-r) := by rw [Real.exp_add]
    _ = Real.exp (-1 : ℝ) ^ n * Real.exp (-r) := by
      rw [show (-((n : ℝ)) : ℝ) = (n : ℝ) * (-1) by ring,
        Real.exp_nat_mul]
    _ ≤ expNegOneUpper2498 ^ n *
        (expTaylor20 r + expTaylor20Error) := hfactor

end
end ConnesWeilRH.Source.C1ScaledExpRationalEnvelope
