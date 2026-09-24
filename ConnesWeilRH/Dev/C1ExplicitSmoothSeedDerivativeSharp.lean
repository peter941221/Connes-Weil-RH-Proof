import ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeValue

/-!
# The sharp derivative constant for the committed explicit seed

Record 1968 bounded the derivative of the committed seed by the product-rule
constant `4` and recorded that the constant is not sharp: the two derivative
factors of

    smoothSeedRaw x = smoothTransition (x + 2) * smoothTransition (2 - x)

are active on the disjoint windows `(-2, -1)` and `(1, 2)`, where the passive
factor equals `1` and has zero derivative. This file formalizes that split.

The chain is:

* `deriv_smoothTransition_eq_zero_of_one_le` : the transition derivative
  vanishes on `[1, ∞)`, where the transition function is constantly `1`;
* `norm_deriv_smoothSeedRaw_le_two` : the sharp bound. If `x ≤ 1` then the
  second factor has zero derivative, so the derivative is
  `T' (x + 2) * T (2 - x)` and `‖T‖ ≤ 1` gives `2`; if `1 ≤ x` the two roles
  swap. No region with both factors active exists;
* `deriv_smoothTransition_half` : `deriv smoothTransition (1/2) = 2`, the
  equality case of the transition bound;
* `deriv_smoothSeedRaw_neg_three_halves` and `deriv_smoothSeedRaw_three_halves`
  and `norm_deriv_smoothSeedRaw_neg_three_halves` : the bound `2` is attained
  at `x = ±3/2`, so `2` is the exact supremum, not merely an upper bound;
* the complex and `CompactLogTest` packaging carries the constant `2`;
* `derivativeL1_smoothSeed_le_eight` : support radius `2` and sup `2` give
  `derivativeL1 smoothSeed ≤ (2 * 2) * 2 = 8`.

This sharpens the constants `4` and `16` of record 1968. Those statements are
left in place; they remain true, and nothing downstream depends on their being
optimal.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

noncomputable section

/-! ## 1. The transition derivative vanishes where the transition is constant -/

/-- On `[1, ∞)` the transition function is constantly `1`, hence its
derivative vanishes. -/
theorem deriv_smoothTransition_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    deriv Real.smoothTransition y = 0 := by
  rw [deriv_smoothTransition,
    show expNegInvGlue (1 - y) = 0 from expNegInvGlue.zero_of_nonpos (by linarith)]
  simp

/-! ## 2. The sharp seed bound -/

theorem norm_deriv_smoothSeedRaw_le_two (x : ℝ) : ‖deriv smoothSeedRaw x‖ ≤ 2 := by
  have hb (y : ℝ) : ‖Real.smoothTransition y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg y)]
    exact Real.smoothTransition.le_one y
  rw [(hasDerivAt_smoothSeedRaw x).deriv]
  rcases le_total x 1 with hx | hx
  · rw [deriv_smoothTransition_eq_zero_of_one_le (y := 2 - x) (by linarith), mul_zero,
      sub_zero]
    calc ‖deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x)‖
        = ‖deriv Real.smoothTransition (x + 2)‖ * ‖Real.smoothTransition (2 - x)‖ :=
          norm_mul _ _
      _ ≤ 2 * 1 :=
        mul_le_mul (norm_deriv_smoothTransition_le_two _) (hb _) (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  · rw [deriv_smoothTransition_eq_zero_of_one_le (y := x + 2) (by linarith), zero_mul,
      zero_sub]
    calc ‖-(Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x))‖
        = ‖Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x)‖ :=
          norm_neg _
      _ = ‖Real.smoothTransition (x + 2)‖ * ‖deriv Real.smoothTransition (2 - x)‖ :=
          norm_mul _ _
      _ ≤ 1 * 2 :=
        mul_le_mul (hb _) (norm_deriv_smoothTransition_le_two _) (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num

/-! ## 3. The bound is attained -/

/-- The equality case of the transition bound. -/
theorem deriv_smoothTransition_half : deriv Real.smoothTransition (1 / 2) = 2 := by
  have hu : expNegInvGlue (1 / 2) = Real.exp (-2) := by
    rw [expNegInvGlue, if_neg (by norm_num)]
    norm_num
  have hv : expNegInvGlue (1 - 1 / 2) = Real.exp (-2) := by
    rw [expNegInvGlue, if_neg (by norm_num)]
    norm_num
  have h1 : ((1 / 2 : ℝ)⁻¹) ^ 2 = 4 := by norm_num
  have h2 : ((1 - 1 / 2 : ℝ)⁻¹) ^ 2 = 4 := by norm_num
  rw [deriv_smoothTransition, hu, hv, h1, h2]
  have hden : Real.exp (-2) + Real.exp (-2) ≠ 0 := by positivity
  field_simp
  ring

theorem deriv_smoothSeedRaw_neg_three_halves : deriv smoothSeedRaw (-3 / 2) = 2 := by
  rw [(hasDerivAt_smoothSeedRaw (-3 / 2)).deriv]
  rw [show (-3 / 2 : ℝ) + 2 = 1 / 2 by norm_num,
    show (2 : ℝ) - -3 / 2 = 7 / 2 by norm_num,
    deriv_smoothTransition_half,
    deriv_smoothTransition_eq_zero_of_one_le (y := 7 / 2) (by norm_num),
    show Real.smoothTransition (7 / 2) = 1 from
      Real.smoothTransition.one_of_one_le (by norm_num)]
  ring

theorem deriv_smoothSeedRaw_three_halves : deriv smoothSeedRaw (3 / 2) = -2 := by
  rw [(hasDerivAt_smoothSeedRaw (3 / 2)).deriv]
  rw [show (3 / 2 : ℝ) + 2 = 7 / 2 by norm_num,
    show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num,
    deriv_smoothTransition_eq_zero_of_one_le (y := 7 / 2) (by norm_num),
    show Real.smoothTransition (7 / 2) = 1 from
      Real.smoothTransition.one_of_one_le (by norm_num),
    deriv_smoothTransition_half]
  ring

/-- The constant `2` is attained, so it is the exact supremum of the
derivative of the seed. -/
theorem norm_deriv_smoothSeedRaw_neg_three_halves : ‖deriv smoothSeedRaw (-3 / 2)‖ = 2 := by
  rw [deriv_smoothSeedRaw_neg_three_halves, Real.norm_eq_abs]
  norm_num

/-! ## 4. The complex packaging and the L1 budget -/

theorem norm_deriv_smoothSeedComplex_le_two (x : ℝ) :
    ‖deriv smoothSeedComplex x‖ ≤ 2 := by
  have hd : HasDerivAt smoothSeedComplex (((deriv smoothSeedRaw x : ℝ) : ℂ)) x := by
    have h := (hasDerivAt_smoothSeedRaw x).ofReal_comp
    rw [← (hasDerivAt_smoothSeedRaw x).deriv] at h
    simpa [smoothSeedComplex] using h
  rw [hd.deriv, Complex.norm_real]
  exact norm_deriv_smoothSeedRaw_le_two x

theorem norm_deriv_smoothSeed_test_le_two (x : ℝ) :
    ‖deriv (smoothSeed.test : ℝ → ℂ) x‖ ≤ 2 := by
  rw [smoothSeed_test_deriv_eq x]
  exact norm_deriv_smoothSeedComplex_le_two x

theorem derivativeL1_smoothSeed_le_eight : derivativeL1 smoothSeed ≤ 8 := by
  have h := derivativeL1_le_of_support_of_norm_le smoothSeed 2 2
    (by norm_num) (by norm_num)
    support_deriv_smoothSeed_test_subset norm_deriv_smoothSeed_test_le_two
  calc derivativeL1 smoothSeed ≤ (2 * 2) * 2 := h
    _ = 8 := by norm_num

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
