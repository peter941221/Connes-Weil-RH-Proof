import ConnesWeilRH.Dev.C1ExplicitSmoothSeed
import ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeBudget
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# An explicit derivative constant for the committed explicit seed

Record 1967 left one named obligation on the explicit seed: a pointwise bound
for the derivative of `smoothSeedRaw`, to feed the support-times-sup budget
`derivativeL1_le_of_support_of_norm_le`. This file closes that obligation with
an explicit constant.

The chain is:

* `norm_deriv_smoothTransition_le_two` : `‖deriv smoothTransition x‖ ≤ 2`,
  which is sharp (equality at `x = 1/2`);
* `norm_deriv_smoothSeedRaw_le_four` : the two-factor product rule, each
  factor bounded in modulus by `1`, gives the constant `4`. This is not the
  best possible constant: the two derivative factors have disjoint active
  windows, so a region split gives `2` (attained at `x = ±3/2`); the product
  form is what the current chain needs;
* the complex and `CompactLogTest` packaging carries the same constant `4`;
* `derivativeL1_smoothSeed_le_sixteen` : support radius `2` and sup `4` give
  `derivativeL1 smoothSeed ≤ 2 * 2 * 4`.

Nothing here chooses the remaining quantitative constants of the lane
(the shifted-product recurrence, the node product, and the strip contraction
constant stay open).
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open Real
open Polynomial
open expNegInvGlue
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

noncomputable section

open scoped Topology

/-! ## 1. The one-variable inequality

For `u = expNegInvGlue x`, `v = expNegInvGlue (1 - x)` and `0 < x < 1`, the
derivative of the transition function is `uv (a^2 + b^2) / (u + v)^2` with
`a = 1/x`, `b = 1/(1-x)`. Since `(a - 1) (b - 1) = 1`, the bound reduces to
the hyperbolic inequality proved first. -/

theorem cosh_sinh_bound (t : ℝ) :
    2 + 4 * Real.cosh t + 2 * Real.cosh (2 * t) ≤ 8 * Real.cosh (Real.sinh t) ^ 2 := by
  have hcosh2 : Real.cosh (2 * t) = 2 * Real.cosh t ^ 2 - 1 := by
    rw [Real.cosh_two_mul]
    linarith [Real.cosh_sq_sub_sinh_sq t]
  have hsq : Real.cosh (2 * Real.sinh t) = 2 * Real.cosh (Real.sinh t) ^ 2 - 1 := by
    rw [Real.cosh_two_mul]
    linarith [Real.cosh_sq_sub_sinh_sq (Real.sinh t)]
  have hmono : Real.cosh (2 * t) ≤ Real.cosh (2 * Real.sinh t) := by
    rw [Real.cosh_le_cosh]
    have h : |t| ≤ Real.sinh |t| := (Real.self_le_sinh_iff (x := |t|)).mpr (abs_nonneg t)
    calc |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
      _ ≤ 2 * Real.sinh |t| := by linarith
      _ = |2 * Real.sinh t| := by rw [abs_mul, Real.abs_sinh]; norm_num
  have h1 : Real.cosh t ≤ Real.cosh t ^ 2 := by
    nlinarith [Real.one_le_cosh t]
  calc 2 + 4 * Real.cosh t + 2 * Real.cosh (2 * t)
      = 4 * Real.cosh t + 4 * Real.cosh t ^ 2 := by rw [hcosh2]; ring
    _ ≤ 4 * Real.cosh (2 * t) + 4 := by rw [hcosh2]; nlinarith
    _ ≤ 4 * Real.cosh (2 * Real.sinh t) + 4 := by linarith
    _ = 8 * Real.cosh (Real.sinh t) ^ 2 := by rw [hsq]; ring

theorem exp_pair_bound (t : ℝ) :
    (1 + Real.exp t) ^ 2 + (1 + Real.exp (-t)) ^ 2 ≤
      2 * (Real.exp (Real.sinh t) + Real.exp (-Real.sinh t)) ^ 2 := by
  have hmain := cosh_sinh_bound t
  have hexp2 : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add]
    ring
  have hexp2n : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
    rw [show -(2 * t) = -t + -t by ring, Real.exp_add]
    ring
  have hL : (1 + Real.exp t) ^ 2 + (1 + Real.exp (-t)) ^ 2 =
      2 + 4 * Real.cosh t + 2 * Real.cosh (2 * t) := by
    rw [Real.cosh_eq, Real.cosh_eq, hexp2, hexp2n]
    ring
  have hR : 2 * (Real.exp (Real.sinh t) + Real.exp (-Real.sinh t)) ^ 2 =
      8 * Real.cosh (Real.sinh t) ^ 2 := by
    rw [Real.cosh_eq]
    ring
  rw [hL, hR]
  exact hmain

/-- With `a - 1 > 0` and `(a - 1) (b - 1) = 1`, the hypothesis `1 < b` is
implied; it is kept in the statement for symmetry of the two factors. -/
theorem pair_bound_of_shifted_one {a b : ℝ} (ha : 1 < a) (_hb : 1 < b)
    (hab : (a - 1) * (b - 1) = 1) :
    a ^ 2 + b ^ 2 ≤ 2 * (Real.exp ((a - b) / 2) + Real.exp ((b - a) / 2)) ^ 2 := by
  have ha1 : 0 < a - 1 := by linarith
  have hb1 : b - 1 = (a - 1)⁻¹ := by
    field_simp at hab ⊢
    linarith [hab]
  have hexpa : a = 1 + Real.exp (Real.log (a - 1)) := by
    rw [Real.exp_log ha1]
    ring
  have hexpb : b = 1 + Real.exp (-(Real.log (a - 1))) := by
    rw [Real.exp_neg, Real.exp_log ha1]
    linarith [hb1]
  have he : Real.exp (Real.log (a - 1)) = a - 1 := Real.exp_log ha1
  have hen : Real.exp (-(Real.log (a - 1))) = b - 1 := by
    rw [Real.exp_neg, Real.exp_log ha1]
    exact hb1.symm
  have hsinh : Real.sinh (Real.log (a - 1)) = (a - b) / 2 := by
    rw [Real.sinh_eq, he, hen]
    ring
  have hgoal : (1 + Real.exp (Real.log (a - 1))) ^ 2 +
      (1 + Real.exp (-(Real.log (a - 1)))) ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← hexpa, ← hexpb]
  calc a ^ 2 + b ^ 2
      = (1 + Real.exp (Real.log (a - 1))) ^ 2 +
          (1 + Real.exp (-(Real.log (a - 1)))) ^ 2 := hgoal.symm
    _ ≤ 2 * (Real.exp (Real.sinh (Real.log (a - 1))) +
          Real.exp (-Real.sinh (Real.log (a - 1)))) ^ 2 := exp_pair_bound _
    _ = 2 * (Real.exp ((a - b) / 2) + Real.exp ((b - a) / 2)) ^ 2 := by
      have hneg : -((a - b) / 2) = (b - a) / 2 := by ring
      rw [hsinh, hneg]

/-! ## 2. The derivative of the transition function -/

/-- The derivative of `expNegInvGlue` in the exact form `(1/x)^2 * f(x)`
produced by the polynomial-recursion lemma. -/
theorem hasDerivAt_expNegInvGlue (y : ℝ) :
    HasDerivAt expNegInvGlue ((y⁻¹) ^ 2 * expNegInvGlue y) y := by
  simpa [Polynomial.eval_one, Polynomial.derivative_one, Polynomial.eval_pow,
    Polynomial.eval_X, sub_zero, one_mul] using
    hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) y

theorem hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition
      (((x⁻¹) ^ 2 * expNegInvGlue x * expNegInvGlue (1 - x) +
        expNegInvGlue x * ((1 - x)⁻¹) ^ 2 * expNegInvGlue (1 - x)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have h1 := hasDerivAt_expNegInvGlue x
  have h2 : HasDerivAt (fun y : ℝ => expNegInvGlue (1 - y))
      (((1 - x)⁻¹) ^ 2 * expNegInvGlue (1 - x) * (-1)) x := by
    have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
    have hcomp := (hasDerivAt_expNegInvGlue (1 - x)).comp x hinner
    simpa [Function.comp_def] using hcomp
  have hsum : HasDerivAt (fun y : ℝ => expNegInvGlue y + expNegInvGlue (1 - y))
      ((x⁻¹) ^ 2 * expNegInvGlue x +
        ((1 - x)⁻¹) ^ 2 * expNegInvGlue (1 - x) * (-1)) x := by
    have h := h1.add h2
    simpa [Pi.add_apply, Function.comp_def] using h
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have hdiv := h1.div hsum hden
  have hfn : (expNegInvGlue /
      (fun y : ℝ => expNegInvGlue y + expNegInvGlue (1 - y))) = Real.smoothTransition := by
    funext y
    rfl
  rw [hfn] at hdiv
  refine hdiv.congr_deriv ?_
  ring

/-- The derivative of the transition function in the explicit closed form. -/
theorem deriv_smoothTransition (x : ℝ) :
    deriv Real.smoothTransition x =
      (((x⁻¹) ^ 2 * expNegInvGlue x * expNegInvGlue (1 - x) +
        expNegInvGlue x * ((1 - x)⁻¹) ^ 2 * expNegInvGlue (1 - x)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) :=
  (hasDerivAt_smoothTransition x).deriv

theorem norm_deriv_smoothTransition_le_two (x : ℝ) :
    ‖deriv Real.smoothTransition x‖ ≤ 2 := by
  rw [deriv_smoothTransition, Real.norm_eq_abs]
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    simp
  by_cases hx1 : 1 ≤ x
  · rw [show expNegInvGlue (1 - x) = 0 from
      expNegInvGlue.zero_of_nonpos (by linarith)]
    simp
  have hx' : 0 < x := lt_of_not_ge hx
  have hx1' : x < 1 := lt_of_not_ge hx1
  set a : ℝ := x⁻¹ with ha
  set b : ℝ := (1 - x)⁻¹ with hb
  have hu : expNegInvGlue x = Real.exp (-a) := by
    rw [expNegInvGlue, if_neg (not_le.mpr hx'), ha]
  have hv : expNegInvGlue (1 - x) = Real.exp (-b) := by
    rw [expNegInvGlue, if_neg (not_le.mpr (by linarith : (0 : ℝ) < 1 - x)), hb]
  have ha1 : 1 < a := by
    rw [ha]
    exact (one_lt_inv₀ hx').mpr hx1'
  have hb1 : 1 < b := by
    rw [hb]
    exact (one_lt_inv₀ (by linarith : (0 : ℝ) < 1 - x)).mpr (by linarith)
  have hab : (a - 1) * (b - 1) = 1 := by
    rw [ha, hb]
    have hx0 : x ≠ 0 := ne_of_gt hx'
    have hx10 : (1 - x) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - x)
    field_simp
    ring
  have hkey := pair_bound_of_shifted_one ha1 hb1 hab
  have hA : Real.exp (-a) = Real.exp (-(a + b) / 2) * Real.exp ((b - a) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hB : Real.exp (-b) = Real.exp (-(a + b) / 2) * Real.exp ((a - b) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : Real.exp (-a - b) =
      Real.exp (-(a + b) / 2) * Real.exp (-(a + b) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hD : (Real.exp (-a) + Real.exp (-b)) ^ 2 =
      Real.exp (-a - b) * (Real.exp ((a - b) / 2) + Real.exp ((b - a) / 2)) ^ 2 := by
    rw [hA, hB, hE]
    ring
  have hEab : Real.exp (-a - b) = Real.exp (-a) * Real.exp (-b) := by
    have h := Real.exp_add (-a) (-b)
    rw [show -a + -b = -a - b by ring] at h
    exact h
  have hnum : a ^ 2 * Real.exp (-a) * Real.exp (-b) +
      Real.exp (-a) * b ^ 2 * Real.exp (-b) =
      Real.exp (-a - b) * (a ^ 2 + b ^ 2) := by
    rw [hEab]
    ring
  have hval : (a ^ 2 * expNegInvGlue x * expNegInvGlue (1 - x) +
        expNegInvGlue x * b ^ 2 * expNegInvGlue (1 - x)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 =
      (a ^ 2 + b ^ 2) /
        (Real.exp ((a - b) / 2) + Real.exp ((b - a) / 2)) ^ 2 := by
    rw [hu, hv, hD, hnum]
    rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  rw [hval]
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  rw [div_le_iff₀ (by positivity)]
  exact hkey

/-! ## 3. The seed, its complex packaging, and the L1 budget -/

theorem hasDerivAt_smoothSeedRaw (x : ℝ) :
    HasDerivAt smoothSeedRaw
      (deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x) -
        Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x)) x := by
  have hA : HasDerivAt (fun y : ℝ => Real.smoothTransition (y + 2))
      (deriv Real.smoothTransition (x + 2)) x := by
    have hinner : HasDerivAt (fun y : ℝ => y + 2) 1 x :=
      (hasDerivAt_id x).add_const 2
    have hcomp := (hasDerivAt_smoothTransition (x + 2)).comp x hinner
    rw [mul_one] at hcomp
    simpa [Function.comp_def, deriv_smoothTransition] using hcomp
  have hB : HasDerivAt (fun y : ℝ => Real.smoothTransition (2 - y))
      (-deriv Real.smoothTransition (2 - x)) x := by
    have hinner : HasDerivAt (fun y : ℝ => 2 - y) (-1) x := by
      simpa using (hasDerivAt_const (x := x) (c := (2 : ℝ))).sub (hasDerivAt_id x)
    have hcomp := (hasDerivAt_smoothTransition (2 - x)).comp x hinner
    rw [mul_neg_one] at hcomp
    simpa [Function.comp_def, deriv_smoothTransition] using hcomp
  have hmul := hA.mul hB
  have hfun : ((fun y : ℝ => Real.smoothTransition (y + 2)) *
      (fun y : ℝ => Real.smoothTransition (2 - y))) = smoothSeedRaw := by
    funext y
    simp [smoothSeedRaw]
  rw [hfun] at hmul
  have hderiv : deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x) +
        Real.smoothTransition (x + 2) * -deriv Real.smoothTransition (2 - x) =
      deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x) -
        Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x) := by
    ring
  exact hmul.congr_deriv hderiv

theorem norm_deriv_smoothSeedRaw_le_four (x : ℝ) : ‖deriv smoothSeedRaw x‖ ≤ 4 := by
  rw [(hasDerivAt_smoothSeedRaw x).deriv]
  have h1 := norm_deriv_smoothTransition_le_two (x + 2)
  have h2 := norm_deriv_smoothTransition_le_two (2 - x)
  have hb1 : ‖Real.smoothTransition (2 - x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hb2 : ‖Real.smoothTransition (x + 2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hsplit : ‖deriv Real.smoothTransition (x + 2) *
        Real.smoothTransition (2 - x) -
        Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x)‖ ≤
      ‖deriv Real.smoothTransition (x + 2)‖ * ‖Real.smoothTransition (2 - x)‖ +
        ‖Real.smoothTransition (x + 2)‖ *
          ‖deriv Real.smoothTransition (2 - x)‖ := by
    calc ‖deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x) -
          Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x)‖
        ≤ ‖deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x)‖ +
            ‖Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x)‖ :=
          norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  calc ‖deriv Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x) -
        Real.smoothTransition (x + 2) * deriv Real.smoothTransition (2 - x)‖
      ≤ ‖deriv Real.smoothTransition (x + 2)‖ * ‖Real.smoothTransition (2 - x)‖ +
          ‖Real.smoothTransition (x + 2)‖ *
            ‖deriv Real.smoothTransition (2 - x)‖ := hsplit
    _ ≤ 2 * 1 + 1 * 2 := by
      have h3 := mul_le_mul h1 hb1 (norm_nonneg _) (by norm_num)
      have h4 := mul_le_mul hb2 h2 (norm_nonneg _) (by norm_num)
      linarith
    _ = 4 := by norm_num

theorem norm_deriv_smoothSeedComplex_le_four (x : ℝ) :
    ‖deriv smoothSeedComplex x‖ ≤ 4 := by
  have hd : HasDerivAt smoothSeedComplex (((deriv smoothSeedRaw x : ℝ) : ℂ)) x := by
    have h := (hasDerivAt_smoothSeedRaw x).ofReal_comp
    rw [← (hasDerivAt_smoothSeedRaw x).deriv] at h
    simpa [smoothSeedComplex] using h
  rw [hd.deriv, Complex.norm_real]
  exact norm_deriv_smoothSeedRaw_le_four x

theorem smoothSeed_test_deriv_eq (x : ℝ) :
    deriv (smoothSeed.test : ℝ → ℂ) x = deriv smoothSeedComplex x := by
  have hfun : (smoothSeed.test : ℝ → ℂ) = smoothSeedComplex := by
    funext y
    exact smoothSeed_apply y
  rw [hfun]

theorem norm_deriv_smoothSeed_test_le_four (x : ℝ) :
    ‖deriv (smoothSeed.test : ℝ → ℂ) x‖ ≤ 4 := by
  rw [smoothSeed_test_deriv_eq x]
  exact norm_deriv_smoothSeedComplex_le_four x

theorem support_deriv_smoothSeed_test_subset :
    Function.support (deriv (smoothSeed.test : ℝ → ℂ)) ⊆ Set.Icc (-2) 2 := by
  intro x hx
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or] at hmem
  have hz : deriv (smoothSeed.test : ℝ → ℂ) x = 0 := by
    rcases hmem with h | h
    · have hlt : x < -2 := not_le.mp h
      have hev : (smoothSeed.test : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [eventually_lt_nhds hlt] with y hy
        simp only [smoothSeed_apply, smoothSeedComplex,
          smoothSeedRaw_eq_zero_of_le hy.le, Complex.ofReal_zero]
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
    · have hgt : 2 < x := not_le.mp h
      have hev : (smoothSeed.test : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [eventually_gt_nhds hgt] with y hy
        simp only [smoothSeed_apply, smoothSeedComplex,
          smoothSeedRaw_eq_zero_of_ge hy.le, Complex.ofReal_zero]
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  exact hx hz

theorem derivativeL1_smoothSeed_le_sixteen : derivativeL1 smoothSeed ≤ 16 := by
  have h := derivativeL1_le_of_support_of_norm_le smoothSeed 2 4
    (by norm_num) (by norm_num)
    support_deriv_smoothSeed_test_subset norm_deriv_smoothSeed_test_le_four
  calc derivativeL1 smoothSeed ≤ (2 * 2) * 4 := h
    _ = 16 := by norm_num

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
