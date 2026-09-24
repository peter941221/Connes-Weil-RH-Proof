import ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMass

/-!
# The third-order structure of the transition, and why the third rung is not a number

Record 1972 reduced the seed ladder to one function, `T = Real.smoothTransition`:

* `derivOrderL1 j smoothSeed = 2 * ∫ x, ‖iteratedDeriv j T x‖` for `j >= 1`,

and records 1972/1973 pinned the first two rungs to the numbers `2` and `8`.
This file opens the third rung.  Its value is NOT a number: the interior zero
of `T'''` solves a transcendental equation in `tanh`, so the third rung is the
transcendental constant `8 * max T''` on the left half (the accompanying rig
`scripts/seed_third_order_probe_1974.py` reads `78.7283...`, with the peak
`T'' (0.2182558...) = 9.84104...`).  What is formalized here is the ORDER-THREE
STRUCTURE every later step needs:

* the second gain slope `gain'' x = 6 (x⁻¹)^4 + 6 ((1 - x)⁻¹)^4`, its
  derivative brick, its reflection symmetry and its value `192` at `1/2`;
* the reflection identity `T (1 - x) = 1 - T x`;
* the closed form, on `(0, 1)`,

  `T''' x = T x * (1 - T x) *
      (((1 - 2 T x)^2 - 2 T x * (1 - T x)) * gain x ^ 3
        + 3 * (1 - 2 T x) * gain x * slope x + gain'' x)`

  (the middle coefficient `3`, not `2`: the first hand pass of the rig used
  `2 * (1 - 2 T) * gain * slope` and the numerical differentiation of `T''`
  rejects it), together with the reflection `T''' (1 - x) = T''' x` and the
  companion `T'' (1 - x) = -T'' x`;
* the three special values `T''' 0 = T''' 1 = 0` (Fermat, from the committed
  sign of `T''`) and `T''' (1/2) = -16` (exact), plus
  `∫ in 0..1/2, T''' = T'' (1/2) - T'' 0 = 0`;
* the quantitative handle: on any initial segment the norm mass of `T'''`
  absorbs `T'' x`, so the left-half mass does too, and with the reflection
  doubling the half-line mass and record 1972's ladder identity,
  `4 * T'' x ≤ derivOrderL1 3 smoothSeed` for every `0 < x < 1/2` — one point
  value of `T''` certifies a lower bound for the third rung.

What is NOT done: isolating the interior zero of `T'''` (single-peakedness of
`T''` on `[0, 1/2]`), which is exactly what turns `∫ |T'''|` into
`2 * max T''` and would give the third rung a certified rational bracket; the
matching upper bound is likewise open. No `sorry`, no new axioms; the paired
audit records the axiom footprint.
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
open Real
open expNegInvGlue

noncomputable section

open scoped Topology

/-! ## 1. The second slope of the gain -/

/-- The second derivative of the gain, `6 (x⁻¹)^4 + 6 ((1 - x)⁻¹)^4`. -/
def windowGainSecondSlope (x : ℝ) : ℝ := 6 * (x⁻¹) ^ 4 + 6 * ((1 - x)⁻¹) ^ 4

/-- The second gain slope is invariant under the reflection `x ↦ 1 - x`. -/
theorem windowGainSecondSlope_one_sub (y : ℝ) :
    windowGainSecondSlope (1 - y) = windowGainSecondSlope y := by
  unfold windowGainSecondSlope
  ring

/-- On the window the second gain slope is positive. -/
theorem windowGainSecondSlope_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < windowGainSecondSlope x := by
  have h1 : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx0
  have h2 : (0 : ℝ) < (1 - x)⁻¹ := inv_pos.mpr (by linarith)
  have h3 : (0 : ℝ) < (x⁻¹) ^ 4 := pow_pos h1 4
  have h4 : (0 : ℝ) < ((1 - x)⁻¹) ^ 4 := pow_pos h2 4
  unfold windowGainSecondSlope
  linarith

/-- The second gain slope at the centre. -/
theorem windowGainSecondSlope_half_eq : windowGainSecondSlope (1 / 2) = 192 := by
  unfold windowGainSecondSlope
  norm_num

/-- The gain is twice differentiable on the window: the slope has derivative
the second slope. -/
theorem hasDerivAt_windowGainSlope (x : ℝ) (hx0 : x ≠ 0) (hx1 : (1 - x) ≠ 0) :
    HasDerivAt windowGainSlope (windowGainSecondSlope x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (-2 : ℝ) * (y⁻¹) ^ 3) (6 * (x⁻¹) ^ 4) x := by
    have h := ((hasDerivAt_inv hx0).pow 3).const_mul (-2)
    refine h.congr_deriv ?_
    rw [show (3 : ℕ) - 1 = 2 by norm_num, ← inv_pow]
    ring
  have h2 : HasDerivAt (fun y : ℝ => (2 : ℝ) * ((1 - y)⁻¹) ^ 3)
      (6 * ((1 - x)⁻¹) ^ 4) x := by
    have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-((1 - x) ^ 2)⁻¹) (1 - x) :=
      hasDerivAt_inv hx1
    have h := ((hinv.comp x hinner).pow 3).const_mul 2
    refine h.congr_deriv ?_
    change (2 : ℝ) * (3 * (1 - x)⁻¹ ^ (3 - 1) * (-((1 - x) ^ 2)⁻¹ * -1)) =
      6 * ((1 - x)⁻¹) ^ 4
    rw [show (3 : ℕ) - 1 = 2 by norm_num, ← inv_pow]
    ring
  have hsum := h1.add h2
  have hfun : (fun y : ℝ => (-2 : ℝ) * (y⁻¹) ^ 3) +
      (fun y : ℝ => (2 : ℝ) * ((1 - y)⁻¹) ^ 3) = windowGainSlope := by
    funext y
    rfl
  rw [hfun] at hsum
  exact hsum.congr_deriv (by unfold windowGainSecondSlope; ring)

/-! ## 2. The reflection of the transition, and the third derivative -/

/-- The transition is antisymmetric about its centre: `T (1 - x) = 1 - T x`. -/
theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have hden' : expNegInvGlue (1 - x) + expNegInvGlue x ≠ 0 := by
    rw [add_comm]
    exact hden
  unfold Real.smoothTransition
  rw [show (1 : ℝ) - (1 - x) = x by ring]
  field_simp
  ring

/-- The logistic pair is odd under the reflection. -/
theorem one_sub_two_mul_smoothTransition_one_sub (x : ℝ) :
    1 - 2 * Real.smoothTransition (1 - x) = -(1 - 2 * Real.smoothTransition x) := by
  rw [smoothTransition_one_sub]
  ring

/-- The transition at the centre. -/
theorem smoothTransition_half_eq : Real.smoothTransition (1 / 2) = 1 / 2 := by
  have h : expNegInvGlue (1 / 2) ≠ 0 :=
    (expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  unfold Real.smoothTransition
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  field_simp
  ring

/-- The gain at the centre. -/
theorem windowGain_half_point_eq : windowGain (1 / 2) = 8 := by
  unfold windowGain
  norm_num

/-- The gain slope at the centre. -/
theorem windowGainSlope_half_point_eq : windowGainSlope (1 / 2) = 0 := by
  unfold windowGainSlope
  norm_num

/-- The third iterated derivative is the derivative of the second. -/
theorem iteratedDeriv_three_smoothTransition_eq_deriv_deriv :
    iteratedDeriv 3 Real.smoothTransition =
      deriv (iteratedDeriv 2 Real.smoothTransition) := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]

/-- The second derivative of the transition is differentiable on the window,
with the third-derivative closed form. -/
theorem hasDerivAt_iteratedDeriv_two_smoothTransition (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    HasDerivAt (iteratedDeriv 2 Real.smoothTransition)
      (Real.smoothTransition x * (1 - Real.smoothTransition x) *
        (((1 - 2 * Real.smoothTransition x) ^ 2 -
            2 * Real.smoothTransition x * (1 - Real.smoothTransition x)) * windowGain x ^ 3
          + 3 * (1 - 2 * Real.smoothTransition x) * windowGain x * windowGainSlope x
          + windowGainSecondSlope x)) x := by
  have hfe : iteratedDeriv 2 Real.smoothTransition =ᶠ[𝓝 x]
      fun y : ℝ => Real.smoothTransition y * (1 - Real.smoothTransition y) *
        ((1 - 2 * Real.smoothTransition y) * windowGain y ^ 2 + windowGainSlope y) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hx0, hx1⟩] with y hy
    exact iteratedDeriv_two_smoothTransition_eq y hy.1 hy.2
  have hT : HasDerivAt Real.smoothTransition
      (Real.smoothTransition x * (1 - Real.smoothTransition x) * windowGain x) x :=
    (hasDerivAt_smoothTransition x).congr_deriv
      ((deriv_smoothTransition x).symm.trans (deriv_smoothTransition_eq_mul_windowGain x))
  have h1mT : HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition y)
      (-(Real.smoothTransition x * (1 - Real.smoothTransition x) * windowGain x)) x := by
    simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub hT
  have h1m2T : HasDerivAt (fun y : ℝ => 1 - 2 * Real.smoothTransition y)
      (-(2 * (Real.smoothTransition x * (1 - Real.smoothTransition x) * windowGain x))) x := by
    have h := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hT.const_mul 2)
    simpa using h
  have hg := hasDerivAt_windowGain x hx0.ne' (by linarith : (1 - x) ≠ 0)
  have hgs := hasDerivAt_windowGainSlope x hx0.ne' (by linarith : (1 - x) ≠ 0)
  have hg2 : HasDerivAt (fun y : ℝ => windowGain y ^ 2)
      (2 * windowGain x * windowGainSlope x) x := by
    have h := hg.mul hg
    have hfun : windowGain * windowGain = fun y : ℝ => windowGain y ^ 2 := by
      funext y
      rw [Pi.mul_apply, pow_two]
    rw [hfun] at h
    refine h.congr_deriv ?_
    ring
  have hB := (h1m2T.mul hg2).add hgs
  have hprod := (hT.mul h1mT).mul hB
  have hfun : (Real.smoothTransition * fun y : ℝ => 1 - Real.smoothTransition y) *
      ((fun y : ℝ => 1 - 2 * Real.smoothTransition y) *
          (fun y : ℝ => windowGain y ^ 2) + windowGainSlope) =
      fun y : ℝ => Real.smoothTransition y * (1 - Real.smoothTransition y) *
        ((1 - 2 * Real.smoothTransition y) * windowGain y ^ 2 + windowGainSlope y) := by
    funext y
    rfl
  rw [hfun] at hprod
  simp only [Pi.mul_apply, Pi.add_apply] at hprod
  refine (hfe.hasDerivAt_iff).mpr ?_
  exact hprod.congr_deriv (by ring)

/-- The third derivative of the transition, in the gain form. -/
theorem iteratedDeriv_three_smoothTransition_eq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv 3 Real.smoothTransition x =
      Real.smoothTransition x * (1 - Real.smoothTransition x) *
        (((1 - 2 * Real.smoothTransition x) ^ 2 -
            2 * Real.smoothTransition x * (1 - Real.smoothTransition x)) * windowGain x ^ 3
          + 3 * (1 - 2 * Real.smoothTransition x) * windowGain x * windowGainSlope x
          + windowGainSecondSlope x) := by
  rw [iteratedDeriv_three_smoothTransition_eq_deriv_deriv]
  exact (hasDerivAt_iteratedDeriv_two_smoothTransition x hx0 hx1).deriv

/-! ## 3. Reflections of the second and third derivatives -/

/-- The second derivative is odd under the reflection `x ↦ 1 - x`. -/
theorem iteratedDeriv_two_smoothTransition_one_sub (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    iteratedDeriv 2 Real.smoothTransition (1 - x) =
      -iteratedDeriv 2 Real.smoothTransition x := by
  have h0 : 0 < 1 - x := by linarith
  have h1 : 1 - x < 1 := by linarith
  rw [iteratedDeriv_two_smoothTransition_eq (1 - x) h0 h1,
    iteratedDeriv_two_smoothTransition_eq x hx0 hx1,
    smoothTransition_one_sub, windowGain_one_sub, windowGainSlope_one_sub]
  ring

/-- The third derivative is even under the reflection `x ↦ 1 - x`. -/
theorem iteratedDeriv_three_smoothTransition_one_sub (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    iteratedDeriv 3 Real.smoothTransition (1 - x) =
      iteratedDeriv 3 Real.smoothTransition x := by
  have h0 : 0 < 1 - x := by linarith
  have h1 : 1 - x < 1 := by linarith
  rw [iteratedDeriv_three_smoothTransition_eq (1 - x) h0 h1,
    iteratedDeriv_three_smoothTransition_eq x hx0 hx1,
    smoothTransition_one_sub, windowGain_one_sub, windowGainSlope_one_sub,
    windowGainSecondSlope_one_sub]
  ring

/-! ## 4. `T'''` at the special points -/

/-- `T''' (1/2) = -16`, the first nonvanishing special value of the third
derivative. -/
theorem iteratedDeriv_three_smoothTransition_half :
    iteratedDeriv 3 Real.smoothTransition (1 / 2) = -16 := by
  rw [iteratedDeriv_three_smoothTransition_eq (1 / 2) (by norm_num) (by norm_num),
    smoothTransition_half_eq, windowGain_half_point_eq, windowGainSlope_half_point_eq,
    windowGainSecondSlope_half_eq]
  norm_num

/-- `T''` has a minimum at `0`: it vanishes there and is nonnegative on the
left half. -/
theorem isLocalMin_iteratedDeriv_two_smoothTransition :
    IsLocalMin (iteratedDeriv 2 Real.smoothTransition) 0 := by
  refine Filter.eventually_of_mem
    (Ioo_mem_nhds (show (-(1 / 2) : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)) fun y hy => ?_
  rw [iteratedDeriv_two_smoothTransition_zero]
  by_cases h : y ≤ 0
  · rcases lt_or_eq_of_le h with h' | h'
    · rw [iteratedDeriv_smoothTransition_eq_zero_of_lt_zero 2 h']
    · rw [h', iteratedDeriv_two_smoothTransition_zero]
  · exact iteratedDeriv_two_smoothTransition_nonneg (not_le.mp h)
      (by linarith [hy.2])

/-- `T''` has a maximum at `1`: it vanishes there and is nonpositive on the
right half. -/
theorem isLocalMax_iteratedDeriv_two_smoothTransition :
    IsLocalMax (iteratedDeriv 2 Real.smoothTransition) 1 := by
  refine Filter.eventually_of_mem
    (Ioo_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) < 3 / 2 by norm_num)) fun y hy => ?_
  rw [iteratedDeriv_two_smoothTransition_one]
  by_cases h : 1 ≤ y
  · rcases lt_or_eq_of_le h with h' | h'
    · rw [iteratedDeriv_smoothTransition_eq_zero_of_one_lt 2 (by norm_num) h']
    · rw [← h', iteratedDeriv_two_smoothTransition_one]
  · exact iteratedDeriv_two_smoothTransition_nonpos (le_of_lt hy.1)
      (not_le.mp h)

/-- `T''' 0 = 0`, by Fermat's theorem at the minimum of `T''`. -/
theorem iteratedDeriv_three_smoothTransition_zero :
    iteratedDeriv 3 Real.smoothTransition 0 = 0 := by
  rw [iteratedDeriv_three_smoothTransition_eq_deriv_deriv]
  exact isLocalMin_iteratedDeriv_two_smoothTransition.deriv_eq_zero

/-- `T''' 1 = 0`, by Fermat's theorem at the maximum of `T''`. -/
theorem iteratedDeriv_three_smoothTransition_one :
    iteratedDeriv 3 Real.smoothTransition 1 = 0 := by
  rw [iteratedDeriv_three_smoothTransition_eq_deriv_deriv]
  exact isLocalMax_iteratedDeriv_two_smoothTransition.deriv_eq_zero

/-- `T''` rises from `0` to its peak and comes back to `0` at `1/2`, so the
integral of `T'''` over the left half vanishes. -/
theorem integral_iteratedDeriv_three_smoothTransition_left :
    ∫ x in (0 : ℝ)..(1 / 2), iteratedDeriv 3 Real.smoothTransition x = 0 := by
  have hcd : ContDiffOn ℝ 1 (iteratedDeriv 2 Real.smoothTransition)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    (contDiff_one_iteratedDeriv_smoothTransition 2).contDiffOn
  have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← iteratedDeriv_three_smoothTransition_eq_deriv_deriv] at hftc
  rw [hftc, iteratedDeriv_two_smoothTransition_half, iteratedDeriv_two_smoothTransition_zero]
  norm_num

/-! ## 5. The quantitative handle on the third rung -/

/-- The reflected norm of `T'''` agrees with the norm on the closed left half:
the reflection identity extends to the endpoints through the two Fermat
values. -/
theorem norm_iteratedDeriv_three_one_sub {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedDeriv 3 Real.smoothTransition (1 - u)‖ =
      ‖iteratedDeriv 3 Real.smoothTransition u‖ := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, show (1 : ℝ) - 0 = 1 by norm_num, iteratedDeriv_three_smoothTransition_one,
      iteratedDeriv_three_smoothTransition_zero]
  · rcases eq_or_lt_of_le hu.2 with h2 | h2
    · rw [h2, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    · rw [iteratedDeriv_three_smoothTransition_one_sub u h0 (by linarith)]

/-- The norm mass of `T'''` over an initial segment absorbs `T'' x`: the two
are the same integral, and the norm dominates its absolute value. -/
theorem iteratedDeriv_two_le_integral_norm_iteratedDeriv_three (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1 / 2) :
    iteratedDeriv 2 Real.smoothTransition x ≤
      ∫ y in (0 : ℝ)..x, ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
  have hftc : ∫ y in (0 : ℝ)..x, iteratedDeriv 3 Real.smoothTransition y =
      iteratedDeriv 2 Real.smoothTransition x := by
    have hcd : ContDiffOn ℝ 1 (iteratedDeriv 2 Real.smoothTransition) (Set.Icc (0 : ℝ) x) :=
      (contDiff_one_iteratedDeriv_smoothTransition 2).contDiffOn
    have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd (le_of_lt hx0)
    rw [← iteratedDeriv_three_smoothTransition_eq_deriv_deriv] at h
    rw [h, iteratedDeriv_two_smoothTransition_zero, sub_zero]
  have hle := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun y : ℝ => iteratedDeriv 3 Real.smoothTransition y) (le_of_lt hx0)
  rw [hftc, Real.norm_eq_abs,
    abs_of_nonneg (iteratedDeriv_two_smoothTransition_nonneg hx0 (le_of_lt hx1))] at hle
  exact hle

/-- The norm mass of `T'''` over the whole left half absorbs `T'' x` at every
strictly interior point. -/
theorem iteratedDeriv_two_le_integral_norm_iteratedDeriv_three_left (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1 / 2) :
    iteratedDeriv 2 Real.smoothTransition x ≤
      ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
  have h1 := iteratedDeriv_two_le_integral_norm_iteratedDeriv_three x hx0 hx1
  have hcont : Continuous fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition 3).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖)
    (hcont.intervalIntegrable 0 x) (hcont.intervalIntegrable x (1 / 2))
  have hnn : 0 ≤ ∫ y in x..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
    intervalIntegral.integral_nonneg_of_ae (le_of_lt hx1)
      (Filter.Eventually.of_forall fun y => norm_nonneg _)
  linarith [hadd, hnn, h1]

/-- The third rung of the seed ladder is at least `4 * T'' x` at every strictly
interior point of the left half. The third rung is the transcendental constant
`8 * max T''`; this is the two-sided-free half of it, certified through one
point value. -/
theorem derivOrderL1_smoothSeed_three_ge (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    4 * iteratedDeriv 2 Real.smoothTransition x ≤ derivOrderL1 3 smoothSeed := by
  have hhalf := iteratedDeriv_two_le_integral_norm_iteratedDeriv_three_left x hx0 hx1
  have hreflect : ∫ y in (1 / 2 : ℝ)..1, ‖iteratedDeriv 3 Real.smoothTransition y‖ =
      ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (f := fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖) (a := (0 : ℝ))
      (b := 1 / 2) (1 : ℝ)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_zero] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hu
    exact norm_iteratedDeriv_three_one_sub ⟨hu.1, hu.2⟩
  have hoff : ∀ y : ℝ, y ∉ Set.Icc (0 : ℝ) 1 →
      ‖iteratedDeriv 3 Real.smoothTransition y‖ = 0 := by
    intro y hy
    have hzero : iteratedDeriv 3 Real.smoothTransition y = 0 := by
      by_contra hne
      exact hy (support_iteratedDeriv_smoothTransition_subset 3 (by norm_num)
        (Function.mem_support.mpr hne))
    rw [hzero, norm_zero]
  have hcont : Continuous fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition 3).continuous
  have hfull : ∫ y : ℝ, ‖iteratedDeriv 3 Real.smoothTransition y‖ =
      2 * ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
    calc ∫ y : ℝ, ‖iteratedDeriv 3 Real.smoothTransition y‖
        = ∫ y in Set.Icc (0 : ℝ) 1, ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
      _ = ∫ y in (0 : ℝ)..1, ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      _ = (∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖) +
          ∫ y in (1 / 2 : ℝ)..1, ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
          (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            (hcont.intervalIntegrable 0 (1 / 2))
            (hcont.intervalIntegrable (1 / 2) 1)).symm
      _ = (∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖) +
          ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
          rw [hreflect]
      _ = 2 * ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
          ring
  rw [derivOrderL1_smoothSeed_eq 3 (by norm_num), hfull]
  linarith [hhalf]

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
