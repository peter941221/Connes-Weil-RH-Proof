import ConnesWeilRH.Dev.C1ExplicitDerivativeLadder
import ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeSharp
import ConnesWeilRH.Dev.C1ExplicitSmoothSeedMassBudget
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# The seed ladder over the transition function: one function, and the value at order one

Record 1971 left the seed ladder as a bound with a single unknown family, the
sup norms of the iterated derivatives of the committed seed. That seed is a
product of two translates of `Real.smoothTransition`,

    smoothSeedRaw x = smoothTransition (x + 2) * smoothTransition (2 - x),

and the two factors are constant on the regions where the other one is not:
the second factor equals `1` for `x <= 1`, the first one equals `1` for
`x >= -1`. So for every order `j >= 1` the seed derivative is a sum of one
term only, and at every point at most one of the two terms is nonzero:

* `iteratedDeriv_smoothSeedRaw_eq` : for `j >= 1`, the seed derivative is the
  sum `iteratedDeriv j T (x + 2) + (-1)^j * iteratedDeriv j T (2 - x)`;
* `norm_iteratedDeriv_smoothSeed_test_eq` : the norm identity, the two terms
  having disjoint supports inside the seed's window;
* `derivOrderL1_smoothSeed_eq` : integrating against the shift- and
  reflection-invariant measure,
  `derivOrderL1 j smoothSeed = 2 * ∫ x, ‖iteratedDeriv j T x‖`.

The ladder is therefore the transition function's mass doubled, and the
transition function is one function only. At order one it is computable: the
transition is nondecreasing from `0` to `1`, so its derivative is nonnegative
and

* `integral_norm_deriv_smoothTransition_eq_one` : `∫ x, ‖deriv T x‖ = 1`;
* `derivativeL1_smoothSeed_eq_two` : `derivativeL1 smoothSeed = 2`, the exact
  value, sharpening the committed bound `derivativeL1 smoothSeed <= 8`;
* `derivOrderL1_smoothSeed_le_two_mul` : for `j >= 1` the seed oracle reads
  `derivOrderL1 j smoothSeed <= 2 * M` whenever `M` bounds
  `‖iteratedDeriv j T‖` — the factor `2` of record 1971's `4` with the
  transition's sup norms instead of the seed's;
* `l1Mass_shiftedProduct_singleton_smoothSeed_le` : the first numeric rung of
  the seed ladder, `l1Mass (shiftedProduct [a] smoothSeed) <= 2 + 4 * ‖a‖`.

The order-`j` values for `j >= 2` stay as the single integral
`2 * ∫ x, ‖iteratedDeriv j T x‖`; no number is claimed for them.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

noncomputable section

open scoped Topology

/-! ## 1. The transition derivatives vanish at both ends -/

/-- The transition vanishes on `(-∞, 0]`, so all its iterated derivatives
vanish there. -/
theorem iteratedDeriv_smoothTransition_eq_zero_of_lt_zero (j : ℕ) {y : ℝ}
    (hy : y < 0) : iteratedDeriv j Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.le
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_const]
  simp

/-- The transition is constantly `1` on `[1, ∞)`, so its positive-order
iterated derivatives vanish there. -/
theorem iteratedDeriv_smoothTransition_eq_zero_of_one_lt (j : ℕ) (hj : 1 ≤ j)
    {y : ℝ} (hy : 1 < y) : iteratedDeriv j Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 y] (fun _ : ℝ => 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_const,
    if_neg (Nat.one_le_iff_ne_zero.mp hj)]

/-- The support of a positive-order iterated derivative of the transition sits
in `[0, 1]`. -/
theorem support_iteratedDeriv_smoothTransition_subset (j : ℕ) (hj : 1 ≤ j) :
    Function.support (iteratedDeriv j Real.smoothTransition) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨?_, ?_⟩
  · by_contra hcon
    exact hx (iteratedDeriv_smoothTransition_eq_zero_of_lt_zero j (lt_of_not_ge hcon))
  · by_contra hcon
    exact hx (iteratedDeriv_smoothTransition_eq_zero_of_one_lt j hj (lt_of_not_ge hcon))

/-! ## 2. Smoothness in a form that gives continuity and differentiability -/

/-- Every iterated derivative of the transition is `C^1`. -/
theorem contDiff_one_iteratedDeriv_smoothTransition (j : ℕ) :
    ContDiff ℝ (1 : ℕ∞) (iteratedDeriv j Real.smoothTransition) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv' 1 j
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).of_le
      (WithTop.coe_le_coe.mpr le_top))

/-- Every iterated derivative of the committed seed is `C^1`. -/
theorem contDiff_one_iteratedDeriv_smoothSeedRaw (j : ℕ) :
    ContDiff ℝ (1 : ℕ∞) (iteratedDeriv j smoothSeedRaw) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv' 1 j
    (smoothSeedRaw_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))

theorem differentiable_iteratedDeriv_smoothSeedRaw (j : ℕ) :
    Differentiable ℝ (iteratedDeriv j smoothSeedRaw) :=
  (contDiff_one_iteratedDeriv_smoothSeedRaw j).differentiable one_ne_zero

/-! ## 3. The complex packaging carries the iterated derivatives -/

/-- A differentiable real function, read as a complex function, has the
coerced derivative. -/
theorem deriv_ofReal_comp_of_differentiableAt {u : ℝ → ℝ} {x : ℝ}
    (hu : DifferentiableAt ℝ u x) :
    deriv (fun y : ℝ => (u y : ℂ)) x = ((deriv u x : ℝ) : ℂ) :=
  (hu.hasDerivAt.ofReal_comp).deriv

/-- The committed complex seed has the coerced iterated derivatives of the real
seed. -/
theorem iteratedDeriv_smoothSeedComplex_eq (j : ℕ) (x : ℝ) :
    iteratedDeriv j smoothSeedComplex x = ((iteratedDeriv j smoothSeedRaw x : ℝ) : ℂ) := by
  induction j generalizing x with
  | zero =>
      rw [iteratedDeriv_zero]
      rfl
  | succ j ih =>
      have hf : iteratedDeriv j smoothSeedComplex =
          (fun y : ℝ => ((iteratedDeriv j smoothSeedRaw y : ℝ) : ℂ)) := funext ih
      rw [iteratedDeriv_succ, hf,
        deriv_ofReal_comp_of_differentiableAt
          ((differentiable_iteratedDeriv_smoothSeedRaw j).differentiableAt),
        ← iteratedDeriv_succ]

/-! ## 4. The pointwise reduction of the seed derivatives -/

/-- For every positive order the seed derivative splits into the two terms,
each of which lives on one side of the window. -/
theorem iteratedDeriv_smoothSeedRaw_eq (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    iteratedDeriv j smoothSeedRaw x =
      iteratedDeriv j Real.smoothTransition (x + 2) +
        (-1 : ℝ) ^ j * iteratedDeriv j Real.smoothTransition (2 - x) := by
  by_cases hx : (1 : ℝ) ≤ x
  · have hev : smoothSeedRaw =ᶠ[𝓝 x] (fun y : ℝ => Real.smoothTransition (2 - y)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show (-1 : ℝ) < x by linarith)] with y hy
      simp only [smoothSeedRaw]
      rw [Real.smoothTransition.one_of_one_le
        (show (1 : ℝ) ≤ y + 2 by linarith [Set.mem_Ioi.mp hy]), one_mul]
    rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_comp_const_sub]
    rw [iteratedDeriv_smoothTransition_eq_zero_of_one_lt j hj (show (1 : ℝ) < x + 2 by linarith),
      zero_add]
    simp only [smul_eq_mul]
  · have hxlt : x < 1 := not_le.mp hx
    have hev : smoothSeedRaw =ᶠ[𝓝 x] (fun y : ℝ => Real.smoothTransition (y + 2)) := by
      filter_upwards [isOpen_Iio.mem_nhds hxlt] with y hy
      simp only [smoothSeedRaw]
      rw [Real.smoothTransition.one_of_one_le
        (show (1 : ℝ) ≤ 2 - y by linarith [Set.mem_Iio.mp hy]), mul_one]
    rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_comp_add_const]
    rw [iteratedDeriv_smoothTransition_eq_zero_of_one_lt j hj (show (1 : ℝ) < 2 - x by linarith),
      mul_zero, add_zero]

/-- At every point at most one of the two terms is nonzero, so the norm of the
seed derivative is the sum of the two transition-derivative norms. -/
theorem norm_iteratedDeriv_smoothSeedRaw_eq (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    ‖iteratedDeriv j smoothSeedRaw x‖ =
      ‖iteratedDeriv j Real.smoothTransition (x + 2)‖ +
        ‖iteratedDeriv j Real.smoothTransition (2 - x)‖ := by
  rw [iteratedDeriv_smoothSeedRaw_eq j hj x]
  by_cases hx : (1 : ℝ) ≤ x
  · have hz : iteratedDeriv j Real.smoothTransition (x + 2) = 0 :=
      iteratedDeriv_smoothTransition_eq_zero_of_one_lt j hj (by linarith)
    rw [hz, zero_add, norm_zero, zero_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
  · have hz : iteratedDeriv j Real.smoothTransition (2 - x) = 0 :=
      iteratedDeriv_smoothTransition_eq_zero_of_one_lt j hj (by linarith)
    rw [hz, mul_zero, add_zero, norm_zero, add_zero]

/-- The same identity for the committed complex seed. -/
theorem norm_iteratedDeriv_smoothSeed_test_eq (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    ‖iteratedDeriv j (smoothSeed.test : ℝ → ℂ) x‖ =
      ‖iteratedDeriv j Real.smoothTransition (x + 2)‖ +
        ‖iteratedDeriv j Real.smoothTransition (2 - x)‖ := by
  have hfun : (smoothSeed.test : ℝ → ℂ) = smoothSeedComplex := by
    funext y
    exact smoothSeed_apply y
  rw [hfun, iteratedDeriv_smoothSeedComplex_eq j x, Complex.norm_real]
  exact norm_iteratedDeriv_smoothSeedRaw_eq j hj x

/-! ## 5. Integrability of the two shifted pieces -/

theorem integrable_norm_iteratedDeriv_smoothTransition_add (j : ℕ) (hj : 1 ≤ j) (c : ℝ) :
    Integrable (fun x : ℝ => ‖iteratedDeriv j Real.smoothTransition (x + c)‖) := by
  have hcont : Continuous fun x : ℝ => iteratedDeriv j Real.smoothTransition (x + c) :=
    (contDiff_one_iteratedDeriv_smoothTransition j).continuous.comp
      (continuous_id.add continuous_const)
  refine (hcont.norm).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -c) (b := 1 - c)) fun x hx => ?_)
  have hx' : iteratedDeriv j Real.smoothTransition (x + c) ≠ 0 := by
    simpa only [Function.mem_support, norm_ne_zero_iff] using hx
  have hmem := support_iteratedDeriv_smoothTransition_subset j hj (Function.mem_support.mpr hx')
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem integrable_norm_iteratedDeriv_smoothTransition_sub (j : ℕ) (hj : 1 ≤ j) (c : ℝ) :
    Integrable (fun x : ℝ => ‖iteratedDeriv j Real.smoothTransition (c - x)‖) := by
  have hcont : Continuous fun x : ℝ => iteratedDeriv j Real.smoothTransition (c - x) :=
    (contDiff_one_iteratedDeriv_smoothTransition j).continuous.comp
      (continuous_const.sub continuous_id)
  refine (hcont.norm).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := c - 1) (b := c)) fun x hx => ?_)
  have hx' : iteratedDeriv j Real.smoothTransition (c - x) ≠ 0 := by
    simpa only [Function.mem_support, norm_ne_zero_iff] using hx
  have hmem := support_iteratedDeriv_smoothTransition_subset j hj (Function.mem_support.mpr hx')
  exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩

/-! ## 6. The ladder over the transition function -/

/-- The seed ladder is the transition mass doubled, at every positive order. -/
theorem derivOrderL1_smoothSeed_eq (j : ℕ) (hj : 1 ≤ j) :
    derivOrderL1 j smoothSeed = 2 * ∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ := by
  have hcongr : (∫ x : ℝ, ‖iteratedDeriv j (smoothSeed.test : ℝ → ℂ) x‖) =
      ∫ x : ℝ, (‖iteratedDeriv j Real.smoothTransition (x + 2)‖ +
        ‖iteratedDeriv j Real.smoothTransition (2 - x)‖) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      norm_iteratedDeriv_smoothSeed_test_eq j hj x)
  have hshift : (∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition (2 - x)‖) =
      ∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ := by
    rw [show (∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition (2 - x)‖) =
        ∫ x : ℝ, (fun t : ℝ => ‖iteratedDeriv j Real.smoothTransition (-t)‖) (x - 2) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change ‖iteratedDeriv j Real.smoothTransition (2 - x)‖ =
          ‖iteratedDeriv j Real.smoothTransition (-(x - 2))‖
        rw [neg_sub])]
    rw [integral_sub_right_eq_self
      (fun t : ℝ => ‖iteratedDeriv j Real.smoothTransition (-t)‖) 2]
    exact integral_neg_eq_self
      (fun t : ℝ => ‖iteratedDeriv j Real.smoothTransition t‖) volume
  calc derivOrderL1 j smoothSeed
      = ∫ x : ℝ, ‖iteratedDeriv j (smoothSeed.test : ℝ → ℂ) x‖ := rfl
    _ = ∫ x : ℝ, (‖iteratedDeriv j Real.smoothTransition (x + 2)‖ +
          ‖iteratedDeriv j Real.smoothTransition (2 - x)‖) := hcongr
    _ = (∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition (x + 2)‖) +
          (∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition (2 - x)‖) :=
        integral_add (integrable_norm_iteratedDeriv_smoothTransition_add j hj 2)
          (integrable_norm_iteratedDeriv_smoothTransition_sub j hj 2)
    _ = (∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖) +
          (∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖) := by
        rw [integral_add_right_eq_self
          (fun x : ℝ => ‖iteratedDeriv j Real.smoothTransition x‖) 2, hshift]
    _ = 2 * ∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ := by ring

/-! ## 7. The value at order one -/

/-- The transition derivative is nonnegative, read off the committed closed
form. -/
theorem deriv_smoothTransition_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x := by
  rw [deriv_smoothTransition]
  refine div_nonneg (add_nonneg ?_ ?_) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg x))
      (expNegInvGlue.nonneg (1 - x))
  · exact mul_nonneg (mul_nonneg (expNegInvGlue.nonneg x) (sq_nonneg _))
      (expNegInvGlue.nonneg (1 - x))

/-- The transition derivative is supported in `[0, 1]`. -/
theorem support_deriv_smoothTransition_subset :
    Function.support (deriv Real.smoothTransition) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have h : deriv Real.smoothTransition x = 0 := by
      have h1 := iteratedDeriv_smoothTransition_eq_zero_of_lt_zero 1 (lt_of_not_ge hcon)
      rwa [iteratedDeriv_one] at h1
    exact hx h
  · by_contra hcon
    exact hx (deriv_smoothTransition_eq_zero_of_one_le (le_of_lt (lt_of_not_ge hcon)))

/-- The transition mass at order one is exactly `1`: the transition rises from
`0` to `1`. -/
theorem integral_norm_deriv_smoothTransition_eq_one :
    ∫ x : ℝ, ‖deriv Real.smoothTransition x‖ = 1 := by
  have hoff : ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) 1 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have hx' : x < 0 ∨ 1 < x := by
      have := not_and_or.mp fun h => hx (Set.mem_Icc.mpr h)
      exact this.imp not_le.mp not_le.mp
    rcases hx' with hlt | hgt
    · have h1 := iteratedDeriv_smoothTransition_eq_zero_of_lt_zero 1 hlt
      rwa [iteratedDeriv_one] at h1
    · exact deriv_smoothTransition_eq_zero_of_one_le hgt.le
  calc ∫ x : ℝ, ‖deriv Real.smoothTransition x‖
      = ∫ x : ℝ, deriv Real.smoothTransition x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          change ‖deriv Real.smoothTransition x‖ = deriv Real.smoothTransition x
          rw [Real.norm_eq_abs, abs_of_nonneg (deriv_smoothTransition_nonneg x)])
    _ = ∫ x in Set.Icc (0 : ℝ) 1, deriv Real.smoothTransition x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
    _ = ∫ x in (0 : ℝ)..1, deriv Real.smoothTransition x := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    _ = Real.smoothTransition 1 - Real.smoothTransition 0 :=
        intervalIntegral.integral_deriv_of_contDiffOn_Icc
          ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).contDiffOn)
          (show (0 : ℝ) ≤ 1 by norm_num)
    _ = 1 := by simp

/-- The committed bound `derivativeL1 smoothSeed <= 8` is not sharp: the value
is exactly `2`. -/
theorem derivativeL1_smoothSeed_eq_two : derivativeL1 smoothSeed = 2 := by
  rw [← derivOrderL1_one, derivOrderL1_smoothSeed_eq 1 le_rfl]
  have hbridge : (∫ x : ℝ, ‖iteratedDeriv 1 Real.smoothTransition x‖) =
      ∫ x : ℝ, ‖deriv Real.smoothTransition x‖ := by
    simp only [iteratedDeriv_one]
  rw [hbridge, integral_norm_deriv_smoothTransition_eq_one]
  norm_num

/-! ## 8. The seed oracle with the transition's sup norms -/

theorem derivOrderL1_smoothSeed_le_two_mul (j : ℕ) (hj : 1 ≤ j) {M : ℝ}
    (hM : ∀ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ ≤ M) :
    derivOrderL1 j smoothSeed ≤ 2 * M := by
  rw [derivOrderL1_smoothSeed_eq j hj]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  let bound : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => M)
  have hleft : Integrable fun x : ℝ => ‖iteratedDeriv j Real.smoothTransition x‖ := by
    simpa using integrable_norm_iteratedDeriv_smoothTransition_add j hj 0
  have hright : Integrable bound := by
    exact (integrableOn_const (μ := volume) (C := M) (hs := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hpoint : ∀ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ ≤ bound x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simp only [bound, Set.indicator_of_mem hx]
      exact hM x
    · simp only [bound, Set.indicator, hx, ↓reduceIte]
      have hzero : iteratedDeriv j Real.smoothTransition x = 0 := by
        by_contra hne
        exact hx (support_iteratedDeriv_smoothTransition_subset j hj
          (Function.mem_support.mpr hne))
      simp [hzero]
  calc ∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ ≤ ∫ x : ℝ, bound x :=
        integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = M := by
        rw [show bound = Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => M) by rfl,
          integral_indicator_const M measurableSet_Icc,
          Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        simp only [smul_eq_mul]
        ring

/-- The first numerically bounded rung of the seed ladder: a one-node shifted
product costs `2 + 4 ‖a‖`. -/
theorem l1Mass_shiftedProduct_singleton_smoothSeed_le (a : ℂ) :
    l1Mass (shiftedProduct [a] smoothSeed) ≤ 2 + 4 * ‖a‖ := by
  have h := l1Mass_shiftedProduct_le_ladder [a] smoothSeed
  simp only [ladderBound_cons, ladderBound_nil, Nat.zero_add] at h
  rw [derivOrderL1_one, derivativeL1_smoothSeed_eq_two, derivOrderL1_zero] at h
  calc l1Mass (shiftedProduct [a] smoothSeed) ≤ 2 + ‖a‖ * l1Mass smoothSeed := h
    _ ≤ 2 + ‖a‖ * 4 := by
        have h4 := mul_le_mul_of_nonneg_left smoothSeed_l1Mass_le_four (norm_nonneg a)
        linarith
    _ = 2 + 4 * ‖a‖ := by ring

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
