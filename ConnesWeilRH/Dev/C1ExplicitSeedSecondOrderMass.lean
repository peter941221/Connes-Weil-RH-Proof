import ConnesWeilRH.Dev.C1ExplicitSeedTransitionReduction

/-!
# The second rung of the seed derivative ladder is exactly eight

Record 1972 collapsed the whole derivative ladder of the committed explicit
seed onto the single Mathlib function `Real.smoothTransition` (`T`):

* `derivOrderL1 j smoothSeed = 2 * ∫ x, ‖iteratedDeriv j T x‖` for `j >= 1`,

and pinned the FIRST rung to an exact value, `derivativeL1 smoothSeed = 2`.
This file pins the SECOND rung: `derivOrderL1 2 smoothSeed = 8`.

The chain is:

* the committed closed form of the transition derivative factors as
  `deriv T = T * (1 - T) * gain` with `gain x = (x⁻¹)^2 + ((1 - x)⁻¹)^2`;
* differentiating once more gives, on `(0, 1)`, the pointwise formula
  `T'' x = T x * (1 - T x) * ((1 - 2 T x) * gain x ^ 2 + slope x)`, where
  `slope` is the derivative of the gain;
* on `(0, 1)` the pair `1 - 2 T` is the logistic ratio
  `(exp w - 1) / (exp w + 1)` with `w = (1 - 2 x) / (x * (1 - x))`, and the
  elementary convexity bound `1 + v <= exp v` turns into the lower bound
  `v / (v + 2) <= (exp v - 1) / (exp v + 1)`;
* a polynomial comparison in `s = |2 x - 1|` shows that the gain ratio
  `slope / gain ^ 2 = s (s^2 + 3) (1 - s^2) / (2 (1 + s^2)^2)` is dominated by
  the logistic ratio at `4 s / (1 - s^2)`, so `T''` has the sign of `1 - 2 x`;
* the values of `T''` at `0`, at `1`, and at `1/2` are zero by Fermat's
  theorem, applied to the committed facts `0 <= deriv T` (global minimum at
  `0` and at `1`) and `deriv T (1/2) = 2` with `deriv T <= 2` (global
  maximum);
* the fundamental theorem of calculus gives `∫ in 0..1/2, T'' = 2` and
  `∫ in 1/2..1, T'' = -2`, and the sign makes the absolute-value mass `4`:

  `derivOrderL1 2 smoothSeed = 2 * 4 = 8`.

Order `j >= 3` stays the explicit integral `2 * ∫ x, ‖iteratedDeriv j T x‖`.
No `sorry`, no new axioms; the paired audit file records the axiom footprint.
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

/-! ## 1. The gain of the transition derivative -/

/-- The logarithmic gain `(x⁻¹)^2 + ((1 - x)⁻¹)^2` of the transition
window. -/
def windowGain (x : ℝ) : ℝ := (x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2

/-- The derivative of the gain, `-2 (x⁻¹)^3 + 2 ((1 - x)⁻¹)^3`, named so that
the second-derivative formula stays readable. -/
def windowGainSlope (x : ℝ) : ℝ := -2 * (x⁻¹) ^ 3 + 2 * ((1 - x)⁻¹) ^ 3

/-- The committed closed form of the transition derivative factors through the
logistic pair `T (1 - T)` times the gain. -/
theorem deriv_smoothTransition_eq_mul_windowGain (x : ℝ) :
    deriv Real.smoothTransition x =
      Real.smoothTransition x * (1 - Real.smoothTransition x) * windowGain x := by
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  rw [deriv_smoothTransition]
  unfold Real.smoothTransition windowGain
  rw [show 1 - expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x)) =
      expNegInvGlue (1 - x) / (expNegInvGlue x + expNegInvGlue (1 - x)) by
    field_simp
    ring]
  field_simp

/-- At the left end the transition derivative vanishes. -/
theorem deriv_smoothTransition_zero : deriv Real.smoothTransition 0 = 0 := by
  rw [deriv_smoothTransition, expNegInvGlue.zero_of_nonpos (le_refl (0 : ℝ))]
  simp

/-- The gain is invariant under the reflection `x ↦ 1 - x`. -/
theorem windowGain_one_sub (y : ℝ) : windowGain (1 - y) = windowGain y := by
  unfold windowGain
  ring

/-- The gain slope is odd under the reflection `x ↦ 1 - x`. -/
theorem windowGainSlope_one_sub (y : ℝ) : windowGainSlope (1 - y) = -windowGainSlope y := by
  unfold windowGainSlope
  ring

/-- The gain is differentiable on the window, with derivative the slope. -/
theorem hasDerivAt_windowGain (x : ℝ) (hx0 : x ≠ 0) (hx1 : (1 - x) ≠ 0) :
    HasDerivAt windowGain (windowGainSlope x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y⁻¹) ^ 2) (-2 * (x⁻¹) ^ 3) x := by
    have h := (hasDerivAt_inv hx0).pow 2
    refine h.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, ← inv_pow]
    ring
  have h2 : HasDerivAt (fun y : ℝ => ((1 - y)⁻¹) ^ 2) (2 * ((1 - x)⁻¹) ^ 3) x := by
    have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-((1 - x) ^ 2)⁻¹) (1 - x) :=
      hasDerivAt_inv hx1
    have h := (hinv.comp x hinner).pow 2
    refine h.congr_deriv ?_
    change 2 * (1 - x)⁻¹ ^ (2 - 1) * (-((1 - x) ^ 2)⁻¹ * -1) = 2 * ((1 - x)⁻¹) ^ 3
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, ← inv_pow]
    ring
  have hsum := h1.add h2
  have hfun : (fun y : ℝ => (y⁻¹) ^ 2) + (fun y : ℝ => ((1 - y)⁻¹) ^ 2) = windowGain := by
    funext y
    rfl
  rw [hfun] at hsum
  exact hsum.congr_deriv (by
    unfold windowGainSlope
    ring)

/-! ## 2. The logistic form of `1 - 2 T`, and its exponential bound -/

/-- On the open window, `1 - 2 T` is the logistic ratio in the exponential
variable `w = (1 - 2 x) / (x * (1 - x))`. -/
theorem one_sub_two_mul_smoothTransition_eq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    1 - 2 * Real.smoothTransition x =
      (Real.exp ((1 - 2 * x) / (x * (1 - x))) - 1) /
        (Real.exp ((1 - 2 * x) / (x * (1 - x))) + 1) := by
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have h1x : (1 - x) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - x)
  have hu : expNegInvGlue x = Real.exp (-x⁻¹) := by
    rw [expNegInvGlue, if_neg (not_le.mpr hx0)]
  have hv : expNegInvGlue (1 - x) = Real.exp (-(1 - x)⁻¹) := by
    rw [expNegInvGlue, if_neg (not_le.mpr (by linarith : (0 : ℝ) < 1 - x))]
  have hve : expNegInvGlue (1 - x) =
      Real.exp ((1 - 2 * x) / (x * (1 - x))) * expNegInvGlue x := by
    rw [hv, hu, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hexp : (0 : ℝ) < Real.exp ((1 - 2 * x) / (x * (1 - x))) := Real.exp_pos _
  have hu0 : expNegInvGlue x ≠ 0 := by
    rw [hu]
    exact Real.exp_ne_zero _
  have hden : expNegInvGlue x +
      Real.exp ((1 - 2 * x) / (x * (1 - x))) * expNegInvGlue x ≠ 0 := by
    have hfac : expNegInvGlue x +
        Real.exp ((1 - 2 * x) / (x * (1 - x))) * expNegInvGlue x =
        expNegInvGlue x * (1 + Real.exp ((1 - 2 * x) / (x * (1 - x)))) := by
      ring
    rw [hfac]
    exact mul_ne_zero hu0 (by linarith : (0 : ℝ) <
      1 + Real.exp ((1 - 2 * x) / (x * (1 - x)))).ne'
  have he1 : Real.exp ((1 - 2 * x) / (x * (1 - x))) + 1 ≠ 0 := by
    have h := hexp
    linarith
  unfold Real.smoothTransition
  rw [hve]
  field_simp
  ring

/-- The companion identity at `-w` of the logistic ratio. -/
theorem exp_neg_sub_one_div_exp_neg_add_one (v : ℝ) :
    (Real.exp (-v) - 1) / (Real.exp (-v) + 1) =
      -((Real.exp v - 1) / (Real.exp v + 1)) := by
  have h1 : Real.exp (-v) * Real.exp v = 1 := by
    rw [← Real.exp_add]
    simp
  have hne1 : Real.exp (-v) + 1 ≠ 0 := by
    have h := Real.exp_pos (-v)
    linarith
  have hne2 : Real.exp v + 1 ≠ 0 := by
    have h := Real.exp_pos v
    linarith
  field_simp
  nlinarith [h1]

/-- The elementary convexity bound `1 + v <= exp v`, in logistic form. -/
theorem self_div_add_two_le_exp_ratio (v : ℝ) (hv : 0 ≤ v) :
    v / (v + 2) ≤ (Real.exp v - 1) / (Real.exp v + 1) := by
  have h2 : (0 : ℝ) < v + 2 := by linarith
  have h3 : (0 : ℝ) < Real.exp v + 1 := by
    have h := Real.exp_pos v
    linarith
  rw [div_le_iff₀ h2, div_mul_eq_mul_div, le_div_iff₀ h3]
  nlinarith [Real.add_one_le_exp v]

/-- The polynomial comparison: at `λ = 4 s / (1 - s^2)` the logistic ratio
beats the gain ratio `s (s^2 + 3) (1 - s^2) / (2 (1 + s^2)^2)`. -/
theorem windowGain_ratio_lt_exp_ratio (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2) <
      (Real.exp (4 * s / (1 - s ^ 2)) - 1) / (Real.exp (4 * s / (1 - s ^ 2)) + 1) := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hstep : s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2) <
      2 * s / (1 + 2 * s - s ^ 2) := by
    have hden1 : (0 : ℝ) < 2 * (1 + s ^ 2) ^ 2 := by positivity
    have hden2 : (0 : ℝ) < 1 + 2 * s - s ^ 2 := by nlinarith
    rw [div_lt_iff₀ hden1, div_mul_eq_mul_div, lt_div_iff₀ hden2]
    have hpoly : (s ^ 2 + 3) * (1 - s ^ 2) * (1 + 2 * s - s ^ 2) <
        4 * (1 + s ^ 2) ^ 2 := by
      have hA : (0 : ℝ) < 13 * s ^ 2 - 6 * s + 1 := by
        nlinarith [sq_nonneg (13 * s - 3)]
      have hB : (0 : ℝ) ≤ s ^ 3 * (4 + 3 * s + 2 * s ^ 2 - s ^ 3) := by
        have hfac : (0 : ℝ) < 4 + 3 * s + 2 * s ^ 2 - s ^ 3 := by
          nlinarith [sq_nonneg s, h0, h1]
        positivity
      nlinarith [hA, hB]
    have hmul := mul_lt_mul_of_pos_left hpoly h0
    nlinarith [hmul]
  have hratio : 2 * s / (1 + 2 * s - s ^ 2) =
      (4 * s / (1 - s ^ 2)) / (4 * s / (1 - s ^ 2) + 2) := by
    have hs2' : 1 - s ^ 2 ≠ 0 := hs2.ne'
    have hden2 : (0 : ℝ) < 1 + 2 * s - s ^ 2 := by nlinarith
    have hdenR : 4 * s / (1 - s ^ 2) + 2 ≠ 0 :=
      (by positivity : (0 : ℝ) < 4 * s / (1 - s ^ 2) + 2).ne'
    field_simp
    ring
  calc s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2)
      < 2 * s / (1 + 2 * s - s ^ 2) := hstep
    _ = (4 * s / (1 - s ^ 2)) / (4 * s / (1 - s ^ 2) + 2) := hratio
    _ ≤ (Real.exp (4 * s / (1 - s ^ 2)) - 1) /
          (Real.exp (4 * s / (1 - s ^ 2)) + 1) :=
        self_div_add_two_le_exp_ratio _ (by positivity)

/-! ## 3. The second derivative of the transition -/

/-- The second iterated derivative of the transition is the derivative of its
derivative. -/
theorem iteratedDeriv_two_smoothTransition_eq_deriv_deriv :
    iteratedDeriv 2 Real.smoothTransition = deriv (deriv Real.smoothTransition) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]

/-- The second derivative of the transition, in the gain form. -/
theorem iteratedDeriv_two_smoothTransition_eq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv 2 Real.smoothTransition x =
      Real.smoothTransition x * (1 - Real.smoothTransition x) *
        ((1 - 2 * Real.smoothTransition x) * windowGain x ^ 2 + windowGainSlope x) := by
  rw [iteratedDeriv_two_smoothTransition_eq_deriv_deriv]
  have hfe : deriv Real.smoothTransition =
      fun y : ℝ => Real.smoothTransition y * (1 - Real.smoothTransition y) *
        windowGain y := by
    funext y
    exact deriv_smoothTransition_eq_mul_windowGain y
  rw [hfe]
  have hT : HasDerivAt Real.smoothTransition
      (Real.smoothTransition x * (1 - Real.smoothTransition x) * windowGain x) x :=
    (hasDerivAt_smoothTransition x).congr_deriv
      ((deriv_smoothTransition x).symm.trans (deriv_smoothTransition_eq_mul_windowGain x))
  have h1mT : HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition y)
      (-(Real.smoothTransition x * (1 - Real.smoothTransition x) * windowGain x)) x := by
    simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub hT
  have hg := hasDerivAt_windowGain x hx0.ne' (by linarith : (1 - x) ≠ 0)
  have hprod := (hT.mul h1mT).mul hg
  have hfun : (Real.smoothTransition * fun y : ℝ => 1 - Real.smoothTransition y) *
      windowGain =
      fun y : ℝ => Real.smoothTransition y * (1 - Real.smoothTransition y) *
        windowGain y := by
    funext y
    rfl
  rw [hfun] at hprod
  simp only [Pi.mul_apply] at hprod
  refine hprod.deriv.trans ?_
  ring

/-! ## 4. The gain data at the standard point `(1 + s) / 2` -/

/-- The gain at `(1 + s) / 2` in the variable `s`. -/
theorem windowGain_half_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGain ((1 + s) / 2) = 8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2 := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - s)
  have h1p : (1 + s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  have hs2 : (1 - s ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
  rw [eq_div_iff (pow_ne_zero 2 hs2)]
  unfold windowGain
  rw [show 1 - (1 + s) / 2 = (1 - s) / 2 by ring, inv_div, inv_div]
  field_simp
  ring

/-- The gain slope at `(1 + s) / 2` in the variable `s`. -/
theorem windowGainSlope_half_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGainSlope ((1 + s) / 2) = 32 * s * (s ^ 2 + 3) / (1 - s ^ 2) ^ 3 := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - s)
  have h1p : (1 + s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  have hs2 : (1 - s ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
  rw [eq_div_iff (pow_ne_zero 3 hs2)]
  unfold windowGainSlope
  rw [show 1 - (1 + s) / 2 = (1 - s) / 2 by ring, inv_div, inv_div]
  field_simp
  ring

/-- The gain slope at the standard point is the gain ratio times the gain
square, the factor that the logistic ratio has to beat. -/
theorem windowGainSlope_div_sq_half_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGainSlope ((1 + s) / 2) =
      (s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2)) *
        windowGain ((1 + s) / 2) ^ 2 := by
  rw [windowGain_half_eq s h0 h1, windowGainSlope_half_eq s h0 h1]
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - s)
  have h1p : (1 + s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  have hs2 : (1 - s ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
  have hp2 : (1 + s ^ 2) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The logistic variable at the standard point. -/
theorem halfPoint_one_sub_two_div (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    (1 - 2 * ((1 + s) / 2)) / (((1 + s) / 2) * (1 - (1 + s) / 2)) =
      -(4 * s / (1 - s ^ 2)) := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - s)
  have h1p : (1 + s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  have hs2 : (1 - s ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
  have hdenL : ((1 + s) / 2) * (1 - (1 + s) / 2) ≠ 0 := by
    apply mul_ne_zero
    · exact div_ne_zero h1p (by norm_num)
    · rw [show 1 - (1 + s) / 2 = (1 - s) / 2 by ring]
      exact div_ne_zero h1s (by norm_num)
  rw [div_eq_iff hdenL]
  rw [show -(4 * s / (1 - s ^ 2)) = -(4 * s) / (1 - s ^ 2) by ring]
  rw [div_mul_eq_mul_div]
  rw [eq_div_iff hs2]
  ring

/-- The logistic variable at the reflected point. -/
theorem reflectPoint_one_sub_two_div (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    (1 - 2 * ((1 - s) / 2)) / (((1 - s) / 2) * (1 - (1 - s) / 2)) =
      4 * s / (1 - s ^ 2) := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - s)
  have h1p : (1 + s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  have hs2 : (1 - s ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
  have hdenL : ((1 - s) / 2) * (1 - (1 - s) / 2) ≠ 0 := by
    apply mul_ne_zero
    · exact div_ne_zero h1s (by norm_num)
    · rw [show 1 - (1 - s) / 2 = (1 + s) / 2 by ring]
      exact div_ne_zero h1p (by norm_num)
  rw [div_eq_iff hdenL]
  rw [div_mul_eq_mul_div]
  rw [eq_div_iff hs2]
  ring

/-! ## 5. `T''` at the three special points, by Fermat's theorem -/

/-- `T'' 0 = 0`: `T'` is nonnegative with `T' 0 = 0`, so `0` is a minimum. -/
theorem iteratedDeriv_two_smoothTransition_zero :
    iteratedDeriv 2 Real.smoothTransition 0 = 0 := by
  have hmin : IsLocalMin (deriv Real.smoothTransition) 0 :=
    Filter.Eventually.of_forall fun x => by
      rw [deriv_smoothTransition_zero]
      exact deriv_smoothTransition_nonneg x
  rw [iteratedDeriv_two_smoothTransition_eq_deriv_deriv]
  exact hmin.deriv_eq_zero

/-- `T'' 1 = 0`: `T'` is nonnegative with `T' 1 = 0`, so `1` is a minimum. -/
theorem iteratedDeriv_two_smoothTransition_one :
    iteratedDeriv 2 Real.smoothTransition 1 = 0 := by
  have hmin : IsLocalMin (deriv Real.smoothTransition) 1 :=
    Filter.Eventually.of_forall fun x => by
      rw [deriv_smoothTransition_eq_zero_of_one_le (le_refl (1 : ℝ))]
      exact deriv_smoothTransition_nonneg x
  rw [iteratedDeriv_two_smoothTransition_eq_deriv_deriv]
  exact hmin.deriv_eq_zero

/-- `T'' (1/2) = 0`: `T'` has `T' (1/2) = 2` and `T' <= 2` everywhere, so
`1/2` is a maximum. -/
theorem iteratedDeriv_two_smoothTransition_half :
    iteratedDeriv 2 Real.smoothTransition (1 / 2) = 0 := by
  have hmax : IsLocalMax (deriv Real.smoothTransition) (1 / 2) :=
    Filter.Eventually.of_forall fun x => by
      rw [deriv_smoothTransition_half]
      have h := norm_deriv_smoothTransition_le_two x
      rw [Real.norm_eq_abs] at h
      exact (abs_le.mp h).2
  rw [iteratedDeriv_two_smoothTransition_eq_deriv_deriv]
  exact hmax.deriv_eq_zero

/-! ## 6. The sign of `T''` -/

/-- On `(0, 1/2]` the second derivative is nonnegative. -/
theorem iteratedDeriv_two_smoothTransition_nonneg {x : ℝ} (hx0 : 0 < x)
    (hx2 : x ≤ 1 / 2) : 0 ≤ iteratedDeriv 2 Real.smoothTransition x := by
  rcases eq_or_lt_of_le hx2 with h | h
  · rw [h]
    exact le_of_eq iteratedDeriv_two_smoothTransition_half.symm
  have hx1 : x < 1 := by linarith
  rw [iteratedDeriv_two_smoothTransition_eq x hx0 hx1]
  set s : ℝ := 1 - 2 * x with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hx_eq : x = (1 - s) / 2 := by rw [hs]; ring
  have hT : 1 - 2 * Real.smoothTransition x =
      (Real.exp (4 * s / (1 - s ^ 2)) - 1) / (Real.exp (4 * s / (1 - s ^ 2)) + 1) := by
    rw [one_sub_two_mul_smoothTransition_eq x hx0 hx1]
    have hW : (1 - 2 * x) / (x * (1 - x)) = 4 * s / (1 - s ^ 2) := by
      rw [hx_eq]
      exact reflectPoint_one_sub_two_div s hs0 hs1
    rw [hW]
  have hgx : windowGain x = 8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2 := by
    rw [hx_eq, show (1 - s) / 2 = 1 - (1 + s) / 2 by ring, windowGain_one_sub]
    exact windowGain_half_eq s hs0 hs1
  have hgpx : windowGainSlope x =
      -((s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2)) * windowGain x ^ 2) := by
    rw [hx_eq, show (1 - s) / 2 = 1 - (1 + s) / 2 by ring, windowGainSlope_one_sub,
      windowGain_one_sub, windowGainSlope_div_sq_half_eq s hs0 hs1]
  have hg2pos : (0 : ℝ) < windowGain x ^ 2 := by
    rw [hgx]
    exact sq_pos_of_ne_zero
      (div_ne_zero (ne_of_gt (by positivity : (0 : ℝ) < 8 * (1 + s ^ 2)))
        (pow_ne_zero 2 (ne_of_gt hs2)))
  have hrewrite : (1 - 2 * Real.smoothTransition x) * windowGain x ^ 2 +
      windowGainSlope x =
      windowGain x ^ 2 * ((Real.exp (4 * s / (1 - s ^ 2)) - 1) /
        (Real.exp (4 * s / (1 - s ^ 2)) + 1) -
        s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2)) := by
    rw [hT, hgpx]
    ring
  rw [hrewrite]
  exact mul_nonneg
    (mul_nonneg (Real.smoothTransition.nonneg x)
      (by linarith [Real.smoothTransition.le_one x]))
    (mul_pos hg2pos (sub_pos.mpr (windowGain_ratio_lt_exp_ratio s hs0 hs1))).le

/-- On `[1/2, 1)` the second derivative is nonpositive. -/
theorem iteratedDeriv_two_smoothTransition_nonpos {x : ℝ} (hx2 : 1 / 2 ≤ x)
    (hx1 : x < 1) : iteratedDeriv 2 Real.smoothTransition x ≤ 0 := by
  rcases eq_or_lt_of_le hx2 with h | h
  · rw [← h]
    exact iteratedDeriv_two_smoothTransition_half.le
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_two_smoothTransition_eq x hx0 hx1]
  set s : ℝ := 2 * x - 1 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hx_eq : x = (1 + s) / 2 := by rw [hs]; ring
  have hT : 1 - 2 * Real.smoothTransition x =
      -((Real.exp (4 * s / (1 - s ^ 2)) - 1) /
        (Real.exp (4 * s / (1 - s ^ 2)) + 1)) := by
    rw [one_sub_two_mul_smoothTransition_eq x hx0 hx1]
    have hW : (1 - 2 * x) / (x * (1 - x)) = -(4 * s / (1 - s ^ 2)) := by
      rw [hx_eq]
      exact halfPoint_one_sub_two_div s hs0 hs1
    rw [hW, exp_neg_sub_one_div_exp_neg_add_one]
  have hgx : windowGain x = 8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2 := by
    rw [hx_eq]
    exact windowGain_half_eq s hs0 hs1
  have hgpx : windowGainSlope x =
      (s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2)) * windowGain x ^ 2 := by
    rw [hx_eq, windowGainSlope_div_sq_half_eq s hs0 hs1]
  have hg2pos : (0 : ℝ) < windowGain x ^ 2 := by
    rw [hgx]
    exact sq_pos_of_ne_zero
      (div_ne_zero (ne_of_gt (by positivity : (0 : ℝ) < 8 * (1 + s ^ 2)))
        (pow_ne_zero 2 (ne_of_gt hs2)))
  have hrewrite : (1 - 2 * Real.smoothTransition x) * windowGain x ^ 2 +
      windowGainSlope x =
      -((windowGain x ^ 2 * ((Real.exp (4 * s / (1 - s ^ 2)) - 1) /
        (Real.exp (4 * s / (1 - s ^ 2)) + 1) -
        s * (s ^ 2 + 3) * (1 - s ^ 2) / (2 * (1 + s ^ 2) ^ 2)))) := by
    rw [hT, hgpx]
    ring
  rw [hrewrite]
  refine mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (Real.smoothTransition.nonneg x)
      (by linarith [Real.smoothTransition.le_one x])) ?_
  linarith [mul_pos hg2pos (sub_pos.mpr (windowGain_ratio_lt_exp_ratio s hs0 hs1))]

/-! ## 7. The absolute-value mass of `T''` -/

/-- On `[0, 1/2]` the absolute value is the function itself. -/
theorem integral_abs_iteratedDeriv_two_smoothTransition_left :
    ∫ x in (0 : ℝ)..(1 / 2), |iteratedDeriv 2 Real.smoothTransition x| =
      ∫ x in (0 : ℝ)..(1 / 2), iteratedDeriv 2 Real.smoothTransition x := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0, iteratedDeriv_two_smoothTransition_zero, abs_zero]
  rcases eq_or_lt_of_le hx.2 with h2 | h2
  · rw [h2, iteratedDeriv_two_smoothTransition_half, abs_zero]
  · rw [abs_of_nonneg (iteratedDeriv_two_smoothTransition_nonneg h0 h2.le)]

/-- On `[1/2, 1]` the absolute value is the negative of the function. -/
theorem integral_abs_iteratedDeriv_two_smoothTransition_right :
    ∫ x in (1 / 2 : ℝ)..1, |iteratedDeriv 2 Real.smoothTransition x| =
      ∫ x in (1 / 2 : ℝ)..1, -iteratedDeriv 2 Real.smoothTransition x := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
  rcases eq_or_lt_of_le hx.1 with h2 | h2
  · rw [← h2, iteratedDeriv_two_smoothTransition_half, abs_zero, neg_zero]
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · rw [h1, iteratedDeriv_two_smoothTransition_one, abs_zero, neg_zero]
  · rw [abs_of_nonpos (iteratedDeriv_two_smoothTransition_nonpos h2.le h1)]

/-- The transition rises from `0` to `1`, so the mass of `T''` over the first
half is `2`. -/
theorem integral_iteratedDeriv_two_smoothTransition_left :
    ∫ x in (0 : ℝ)..(1 / 2), iteratedDeriv 2 Real.smoothTransition x = 2 := by
  have hcd : ContDiffOn ℝ 1 (deriv Real.smoothTransition) (Set.Icc (0 : ℝ) (1 / 2)) := by
    have h : ContDiffOn ℝ 1 (iteratedDeriv 1 Real.smoothTransition) (Set.Icc (0 : ℝ) (1 / 2)) :=
      (contDiff_one_iteratedDeriv_smoothTransition 1).contDiffOn
    rwa [iteratedDeriv_one] at h
  have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← iteratedDeriv_two_smoothTransition_eq_deriv_deriv] at hftc
  rw [hftc, deriv_smoothTransition_half, deriv_smoothTransition_zero]
  norm_num

/-- The transition flattens out at `1`, so the mass of `T''` over the second
half is `-2`. -/
theorem integral_iteratedDeriv_two_smoothTransition_right :
    ∫ x in (1 / 2 : ℝ)..1, iteratedDeriv 2 Real.smoothTransition x = -2 := by
  have hcd : ContDiffOn ℝ 1 (deriv Real.smoothTransition) (Set.Icc (1 / 2 : ℝ) 1) := by
    have h : ContDiffOn ℝ 1 (iteratedDeriv 1 Real.smoothTransition) (Set.Icc (1 / 2 : ℝ) 1) :=
      (contDiff_one_iteratedDeriv_smoothTransition 1).contDiffOn
    rwa [iteratedDeriv_one] at h
  have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd
    (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [← iteratedDeriv_two_smoothTransition_eq_deriv_deriv] at hftc
  rw [hftc, deriv_smoothTransition_eq_zero_of_one_le (le_refl (1 : ℝ)),
    deriv_smoothTransition_half]
  norm_num

/-- The absolute-value mass of `T''` is exactly `4`. -/
theorem integral_abs_iteratedDeriv_two_smoothTransition :
    ∫ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| = 4 := by
  have hoff : ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) 1 →
      |iteratedDeriv 2 Real.smoothTransition x| = 0 := by
    intro x hx
    have hzero : iteratedDeriv 2 Real.smoothTransition x = 0 := by
      by_contra hne
      exact hx (support_iteratedDeriv_smoothTransition_subset 2 (by norm_num)
        (Function.mem_support.mpr hne))
    rw [hzero, abs_zero]
  have hcont : Continuous fun x : ℝ => |iteratedDeriv 2 Real.smoothTransition x| :=
    continuous_abs.comp (contDiff_one_iteratedDeriv_smoothTransition 2).continuous
  calc ∫ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x|
      = ∫ x in Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 Real.smoothTransition x| :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
    _ = ∫ x in (0 : ℝ)..1, |iteratedDeriv 2 Real.smoothTransition x| := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    _ = (∫ x in (0 : ℝ)..(1 / 2), |iteratedDeriv 2 Real.smoothTransition x|) +
        ∫ x in (1 / 2 : ℝ)..1, |iteratedDeriv 2 Real.smoothTransition x| :=
        (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hcont.intervalIntegrable 0 (1 / 2))
          (hcont.intervalIntegrable (1 / 2) 1)).symm
    _ = (∫ x in (0 : ℝ)..(1 / 2), iteratedDeriv 2 Real.smoothTransition x) +
        ∫ x in (1 / 2 : ℝ)..1, -iteratedDeriv 2 Real.smoothTransition x := by
        rw [integral_abs_iteratedDeriv_two_smoothTransition_left,
          integral_abs_iteratedDeriv_two_smoothTransition_right]
    _ = 2 + -(-2) := by
        rw [integral_iteratedDeriv_two_smoothTransition_left,
          intervalIntegral.integral_neg, integral_iteratedDeriv_two_smoothTransition_right]
    _ = 4 := by norm_num

/-! ## 8. The second rung of the seed ladder -/

/-- The committed seed ladder at order two is exactly `8`. -/
theorem derivOrderL1_smoothSeed_two : derivOrderL1 2 smoothSeed = 8 := by
  rw [derivOrderL1_smoothSeed_eq 2 (by norm_num)]
  have hbridge : (∫ x : ℝ, ‖iteratedDeriv 2 Real.smoothTransition x‖) =
      ∫ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| := by
    simp only [Real.norm_eq_abs]
  rw [hbridge, integral_abs_iteratedDeriv_two_smoothTransition]
  norm_num

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
