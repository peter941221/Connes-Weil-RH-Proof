import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderStructure

/-!
# The third-order sign comparison: one explicit one-variable inequality

Record 1974 showed that the third rung of the seed ladder is the transcendental
constant `8 * T'' x*`, `x*` the interior zero of `T'''` on the left half, and
left open the single-peakedness of `T''` -- equivalently the uniqueness of that
zero.  This file reduces that uniqueness to ONE explicit one-variable
comparison.

In the half-width coordinate `s = 1 - 2 x` (so `x = (1 - s) / 2`; the left half
is `0 < s < 1`) the three bracket terms of record 1974's closed form clear to a
quadratic in the logistic variable `u = 1 - 2 T x`:

* the reflected gain values (`windowGain_reflect_eq` and its two companions)
  turn the committed evaluations at `(1 + s) / 2` into evaluations at
  `(1 - s) / 2`, with the new standard-point second slope;
* `thirdOrderBracket s u = 4 * (3 u^2 - 1) * (1 + s^2)^3
    - 12 * u * s * (1 + s^2) * (3 + s^2) * (1 - s^2)
    + 3 * (1 + 6 s^2 + s^4) * (1 - s^2)^2` is
  `thirdOrderLeading s * u^2 - thirdOrderMiddle s * u + thirdOrderConstant s`
  with `thirdOrderLeading s = 12 (1 + s^2)^3 > 0` and
  `thirdOrderConstant s = -1 + s^4 (3 s^4 + 8 s^2 - 42) <= -1 < 0` on `[0, 1]`;
* the clearing identity `(1 - s^2)^6 * bracket = 64 * thirdOrderBracket s u`
  gives the factorization
  `(1 - s^2)^6 * T''' ((1 - s) / 2) =
     64 * (T x * (1 - T x)) * thirdOrderBracket s (1 - 2 T x)`;
* because `leading > 0 > constant`, the quadratic has one positive and one
  negative root, so on `u > 0` its sign is the sign of `u - threshold`, where
  `thirdOrderThreshold s` is the positive root
  `(thirdOrderMiddle s + sqrt (discriminant s)) / (2 * thirdOrderLeading s)`:
  the two sign theorems read
  `0 < T''' x <-> thirdOrderThreshold s < u` and `T''' x < 0 <-> u < thirdOrderThreshold s`.

What is NOT done: the interval certificate for the single crossing
`u s = thirdOrderThreshold s` (the rig `scripts/seed_single_peakedness_probe_1975.py`
locates it at `s* = 0.563488341628`, i.e. `x* = 0.218255829186`, with logistic
value `0.929034992747` and positive margins on either side), and hence the
certified rational bracket for the third rung. No `sorry`, no new axioms; the
paired audit records the axiom footprint.
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

/-! ## 1. The gain values at the reflected half-point -/

/-- The gain at the reflected half-point `(1 - s) / 2`, read off the committed
evaluation at `(1 + s) / 2` through the reflection symmetry. -/
theorem windowGain_reflect_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGain ((1 - s) / 2) = 8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2 := by
  rw [show (1 - s) / 2 = 1 - (1 + s) / 2 by ring, windowGain_one_sub,
    windowGain_half_eq s h0 h1]

/-- The gain slope at the reflected half-point, odd under the reflection. -/
theorem windowGainSlope_reflect_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGainSlope ((1 - s) / 2) = -(32 * s * (s ^ 2 + 3) / (1 - s ^ 2) ^ 3) := by
  rw [show (1 - s) / 2 = 1 - (1 + s) / 2 by ring, windowGainSlope_one_sub,
    windowGainSlope_half_eq s h0 h1]

/-- The second gain slope at the standard point `(1 + s) / 2`.  This is the one
evaluation not already committed: record 1974 pinned `G''` only at `1 / 2`. -/
theorem windowGainSecondSlope_standard_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGainSecondSlope ((1 + s) / 2) = 192 * (1 + 6 * s ^ 2 + s ^ 4) / (1 - s ^ 2) ^ 4 := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - s)
  have h1p : (1 + s) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  have hs2 : (1 - s ^ 2) ≠ 0 := ne_of_gt (by nlinarith : (0 : ℝ) < 1 - s ^ 2)
  unfold windowGainSecondSlope
  rw [show 1 - (1 + s) / 2 = (1 - s) / 2 by ring, inv_div, inv_div, div_pow, div_pow]
  norm_num
  field_simp [h1s, h1p, hs2, pow_ne_zero 2 hs2, pow_ne_zero 4 hs2, pow_ne_zero 4 h1s,
    pow_ne_zero 4 h1p]
  ring

/-- The second gain slope at the reflected half-point, even under the
reflection. -/
theorem windowGainSecondSlope_reflect_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    windowGainSecondSlope ((1 - s) / 2) = 192 * (1 + 6 * s ^ 2 + s ^ 4) / (1 - s ^ 2) ^ 4 := by
  rw [show (1 - s) / 2 = 1 - (1 + s) / 2 by ring, windowGainSecondSlope_one_sub,
    windowGainSecondSlope_standard_eq s h0 h1]

/-! ## 2. The logistic variable at the reflected half-point -/

/-- The logistic normal form: on the left half in the `s` coordinate the
variable `1 - 2 T x` is the logistic pair of `v = 4 s / (1 - s^2)`. -/
theorem one_sub_two_mul_smoothTransition_reflect_eq (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    1 - 2 * Real.smoothTransition ((1 - s) / 2) =
      (Real.exp (4 * s / (1 - s ^ 2)) - 1) / (Real.exp (4 * s / (1 - s ^ 2)) + 1) := by
  have hx0 : (0 : ℝ) < (1 - s) / 2 := by linarith
  have hx1 : (1 - s) / 2 < 1 := by linarith
  rw [one_sub_two_mul_smoothTransition_eq ((1 - s) / 2) hx0 hx1,
    reflectPoint_one_sub_two_div s h0 h1]

/-- The logistic variable is positive on the left half. -/
theorem one_sub_two_mul_smoothTransition_reflect_pos (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    0 < 1 - 2 * Real.smoothTransition ((1 - s) / 2) := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  rw [one_sub_two_mul_smoothTransition_reflect_eq s h0 h1]
  apply div_pos
  · exact sub_pos.mpr (one_lt_exp_iff.mpr (div_pos (by linarith) hs2))
  · exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (by norm_num)

/-! ## 3. The third-order bracket and its coefficients -/

/-- The bracket of the third-order closed form, cleared to the half-width
coordinate: `4 (3 u^2 - 1) (1 + s^2)^3 - 12 u s (1 + s^2) (3 + s^2) (1 - s^2)
+ 3 (1 + 6 s^2 + s^4) (1 - s^2)^2`. -/
def thirdOrderBracket (s u : ℝ) : ℝ :=
  4 * (3 * u ^ 2 - 1) * (1 + s ^ 2) ^ 3
    - 12 * u * s * (1 + s ^ 2) * (3 + s ^ 2) * (1 - s ^ 2)
    + 3 * (1 + 6 * s ^ 2 + s ^ 4) * (1 - s ^ 2) ^ 2

/-- The leading coefficient `alpha s = 12 (1 + s^2)^3`. -/
def thirdOrderLeading (s : ℝ) : ℝ := 12 * (1 + s ^ 2) ^ 3

/-- The middle coefficient `beta s = 12 s (1 + s^2) (3 + s^2) (1 - s^2)`. -/
def thirdOrderMiddle (s : ℝ) : ℝ := 12 * s * (1 + s ^ 2) * (3 + s ^ 2) * (1 - s ^ 2)

/-- The constant coefficient `gamma s = 3 (1 + 6 s^2 + s^4) (1 - s^2)^2 - 4 (1 + s^2)^3`. -/
def thirdOrderConstant (s : ℝ) : ℝ :=
  3 * (1 + 6 * s ^ 2 + s ^ 4) * (1 - s ^ 2) ^ 2 - 4 * (1 + s ^ 2) ^ 3

/-- The degree-two first factor of the closed form in the logistic variable:
`(1 - 2 t)^2 - 2 t (1 - t) = (3 (1 - 2 t)^2 - 1) / 2`. -/
theorem logistic_degree_two_normal_form (t : ℝ) :
    (1 - 2 * t) ^ 2 - 2 * t * (1 - t) = (3 * (1 - 2 * t) ^ 2 - 1) / 2 := by
  ring

/-- The bracket is a quadratic in the logistic variable. -/
theorem thirdOrderBracket_eq_quadratic (s u : ℝ) :
    thirdOrderBracket s u =
      thirdOrderLeading s * u ^ 2 - thirdOrderMiddle s * u + thirdOrderConstant s := by
  unfold thirdOrderBracket thirdOrderLeading thirdOrderMiddle thirdOrderConstant
  ring

/-- The leading coefficient is positive everywhere. -/
theorem thirdOrderLeading_pos (s : ℝ) : 0 < thirdOrderLeading s := by
  have h : (0 : ℝ) < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  unfold thirdOrderLeading
  exact mul_pos (by norm_num) (pow_pos h 3)

/-- The middle coefficient is nonnegative on `[0, 1]`. -/
theorem thirdOrderMiddle_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ thirdOrderMiddle s := by
  unfold thirdOrderMiddle
  refine mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)) ?_
  nlinarith

/-- The constant coefficient is negative on `[0, 1]`: `gamma = -1 + s^4 (3 s^4
+ 8 s^2 - 42)` and the inner bracket is at most `-31`. -/
theorem thirdOrderConstant_neg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    thirdOrderConstant s < 0 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hs4 : s ^ 4 ≤ 1 := by nlinarith [sq_nonneg s]
  have hb : 3 * s ^ 4 + 8 * s ^ 2 - 42 < 0 := by nlinarith
  have hkey : thirdOrderConstant s = -1 + s ^ 4 * (3 * s ^ 4 + 8 * s ^ 2 - 42) := by
    unfold thirdOrderConstant
    ring
  have hprod : s ^ 4 * (3 * s ^ 4 + 8 * s ^ 2 - 42) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hb)
  rw [hkey]
  linarith

/-- The clearing identity: multiplying the cleared bracket by `(1 - s^2)^6`
produces `64` times the quadratic. -/
theorem bracket_clearing (s u : ℝ) (hs1 : 1 - s ^ 2 ≠ 0) :
    (1 - s ^ 2) ^ 6 *
        (((3 * u ^ 2 - 1) / 2) * (8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2) ^ 3
          + 3 * u * (8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2) *
              (-(32 * s * (s ^ 2 + 3) / (1 - s ^ 2) ^ 3))
          + 192 * (1 + 6 * s ^ 2 + s ^ 4) / (1 - s ^ 2) ^ 4) =
      64 * thirdOrderBracket s u := by
  rw [thirdOrderBracket]
  field_simp [hs1, pow_ne_zero 2 hs1, pow_ne_zero 3 hs1, pow_ne_zero 4 hs1,
    pow_ne_zero 6 hs1]
  ring

/-! ## 4. The factorized third derivative on the left half -/

/-- On the left half in the `s` coordinate, the committed third-derivative
closed form factors through the third-order bracket. -/
theorem iteratedDeriv_three_smoothTransition_eq_bracket (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    (1 - s ^ 2) ^ 6 * iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) =
      64 * (Real.smoothTransition ((1 - s) / 2) * (1 - Real.smoothTransition ((1 - s) / 2))) *
        thirdOrderBracket s (1 - 2 * Real.smoothTransition ((1 - s) / 2)) := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hs1 : (1 - s ^ 2) ≠ 0 := ne_of_gt hs2
  have hx0 : (0 : ℝ) < (1 - s) / 2 := by linarith
  have hx1 : (1 - s) / 2 < 1 := by linarith
  rw [iteratedDeriv_three_smoothTransition_eq ((1 - s) / 2) hx0 hx1,
    windowGain_reflect_eq s h0 h1, windowGainSlope_reflect_eq s h0 h1,
    windowGainSecondSlope_reflect_eq s h0 h1]
  set t : ℝ := Real.smoothTransition ((1 - s) / 2) with ht
  set g : ℝ := 8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2 with hg
  set g1 : ℝ := -(32 * s * (s ^ 2 + 3) / (1 - s ^ 2) ^ 3) with hg1
  set g2 : ℝ := 192 * (1 + 6 * s ^ 2 + s ^ 4) / (1 - s ^ 2) ^ 4 with hg2
  rw [logistic_degree_two_normal_form]
  have hclear : (1 - s ^ 2) ^ 6 *
        (((3 * (1 - 2 * t) ^ 2 - 1) / 2) * g ^ 3 + 3 * (1 - 2 * t) * g * g1 + g2) =
      64 * thirdOrderBracket s (1 - 2 * t) := by
    rw [hg, hg1, hg2]
    exact bracket_clearing s (1 - 2 * t) hs1
  rw [show (1 - s ^ 2) ^ 6 *
        (t * (1 - t) * (((3 * (1 - 2 * t) ^ 2 - 1) / 2) * g ^ 3 +
          3 * (1 - 2 * t) * g * g1 + g2)) =
      (t * (1 - t)) * ((1 - s ^ 2) ^ 6 *
        (((3 * (1 - 2 * t) ^ 2 - 1) / 2) * g ^ 3 + 3 * (1 - 2 * t) * g * g1 + g2)) by ring,
    hclear]
  ring

/-! ## 5. The quadratic sign machinery -/

/-- The discriminant identity: `4 a P(u) = (2 a u - b)^2 - (b^2 - 4 a c)`. -/
theorem quadratic_discriminant_identity (a b c u : ℝ) :
    4 * a * (a * u ^ 2 - b * u + c) = (2 * a * u - b) ^ 2 - (b ^ 2 - 4 * a * c) := by
  ring

/-- Sign transfer through a positive left factor.  (The negative counterpart
`mul_neg_iff_of_pos_left` is not in the pinned Mathlib, so it is derived here
from `neg_pos` and `mul_neg`.) -/
theorem mul_neg_of_pos_left_iff (p q : ℝ) (hp : 0 < p) : (p * q < 0 ↔ q < 0) := by
  constructor
  · intro h
    by_contra hq
    exact (not_le_of_gt h) (mul_nonneg (le_of_lt hp) (not_lt.mp hq))
  · intro h
    exact mul_neg_of_pos_of_neg hp h

/-- With `a > 0 > c` the middle coefficient stays below the square root of the
discriminant: `b^2 < b^2 - 4 a c` because `a c < 0`. -/
theorem middle_lt_sqrt {a b c : ℝ} (ha : 0 < a) (hc : c < 0) :
    b < Real.sqrt (b ^ 2 - 4 * a * c) := by
  have hlt : b ^ 2 < b ^ 2 - 4 * a * c := by nlinarith [mul_neg_of_pos_of_neg ha hc]
  by_cases hb : 0 ≤ b
  · exact (Real.lt_sqrt hb).mpr hlt
  · have hb' : b < 0 := not_le.mp hb
    exact lt_of_lt_of_le hb' (Real.sqrt_nonneg _)

/-- The negative sign rule: for `a > 0 > c` and `u > 0`, `P u < 0` exactly
when `u` is below the positive root. -/
theorem quadratic_neg_iff {a b c u : ℝ} (ha : 0 < a) (hc : c < 0) (hu : 0 < u) :
    a * u ^ 2 - b * u + c < 0 ↔
      u < (b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  have h4a : (0 : ℝ) < 4 * a := by linarith
  have hsq : (2 * a * u - b) ^ 2 < b ^ 2 - 4 * a * c ↔ a * u ^ 2 - b * u + c < 0 := by
    constructor
    · intro h
      have h1 : 4 * a * (a * u ^ 2 - b * u + c) < 0 := by
        rw [quadratic_discriminant_identity]
        linarith
      exact (mul_neg_of_pos_left_iff (4 * a) (a * u ^ 2 - b * u + c) h4a).mp h1
    · intro h
      have h1 : 4 * a * (a * u ^ 2 - b * u + c) < 0 :=
        (mul_neg_of_pos_left_iff (4 * a) (a * u ^ 2 - b * u + c) h4a).mpr h
      rw [quadratic_discriminant_identity] at h1
      linarith
  have h2a : (0 : ℝ) < 2 * a := by linarith
  rw [lt_div_iff₀ h2a]
  constructor
  · intro hP
    by_cases hx : 0 ≤ 2 * a * u - b
    · have h2 := (Real.lt_sqrt hx).mpr (hsq.mpr hP)
      linarith
    · have hx' : 2 * a * u - b < 0 := not_le.mp hx
      linarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]
  · intro hlt
    by_cases hx : 0 ≤ 2 * a * u - b
    · have h2 : 2 * a * u - b < Real.sqrt (b ^ 2 - 4 * a * c) := by linarith
      exact hsq.mp ((Real.lt_sqrt hx).mp h2)
    · have hx' : 2 * a * u - b < 0 := not_le.mp hx
      have hau : (0 : ℝ) < a * u := mul_pos ha hu
      have h3 : u * (a * u - b) < 0 := mul_neg_of_pos_of_neg hu (by linarith)
      nlinarith

/-- The positive sign rule: for `a > 0 > c` and `u > 0`, `0 < P u` exactly
when `u` is above the positive root. -/
theorem quadratic_pos_iff {a b c u : ℝ} (ha : 0 < a) (hc : c < 0) (hu : 0 < u) :
    0 < a * u ^ 2 - b * u + c ↔
      (b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) < u := by
  have h4a : (0 : ℝ) < 4 * a := by linarith
  have hgsq : b ^ 2 - 4 * a * c < (2 * a * u - b) ^ 2 ↔ 0 < a * u ^ 2 - b * u + c := by
    constructor
    · intro h
      have h1 : 0 < 4 * a * (a * u ^ 2 - b * u + c) := by
        rw [quadratic_discriminant_identity]
        linarith
      exact (mul_pos_iff_of_pos_left h4a).mp h1
    · intro h
      have h1 : 0 < 4 * a * (a * u ^ 2 - b * u + c) := (mul_pos_iff_of_pos_left h4a).mpr h
      rw [quadratic_discriminant_identity] at h1
      linarith
  have h2a : (0 : ℝ) < 2 * a := by linarith
  rw [div_lt_iff₀ h2a]
  constructor
  · intro hP
    by_cases hx : 0 < 2 * a * u - b
    · have h2 : Real.sqrt (b ^ 2 - 4 * a * c) < 2 * a * u - b :=
        (Real.sqrt_lt' hx).mpr (hgsq.mpr hP)
      linarith
    · have hx' : 2 * a * u - b ≤ 0 := not_lt.mp hx
      have hau : (0 : ℝ) < a * u := mul_pos ha hu
      have h2 : a * u ≤ b := by linarith
      have h3 : a * u ≠ b := by
        intro hab
        have hzero : a * u ^ 2 - b * u + c = c := by
          rw [← hab]
          ring
        linarith
      have h4 : a * u < b := lt_of_le_of_ne h2 h3
      have h5 : u * (a * u - b) < 0 := mul_neg_of_pos_of_neg hu (by linarith)
      nlinarith
  · intro hlt
    by_cases hx : 0 < 2 * a * u - b
    · exact hgsq.mp ((Real.sqrt_lt' hx).mp (by linarith))
    · have hx' : 2 * a * u - b ≤ 0 := not_lt.mp hx
      linarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]

/-! ## 6. The threshold and the two sign theorems -/

/-- The positive root of the third-order bracket: the threshold that the
logistic variable crosses exactly once on the left half. -/
noncomputable def thirdOrderThreshold (s : ℝ) : ℝ :=
  (thirdOrderMiddle s +
      Real.sqrt (thirdOrderMiddle s ^ 2 - 4 * thirdOrderLeading s * thirdOrderConstant s)) /
    (2 * thirdOrderLeading s)

/-- The threshold is positive on `[0, 1]`: with a nonnegative middle
coefficient below the square root of the discriminant, and a positive leading
coefficient, the numerator and the denominator are both positive. -/
theorem thirdOrderThreshold_pos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 < thirdOrderThreshold s := by
  have hb := middle_lt_sqrt (b := thirdOrderMiddle s) (thirdOrderLeading_pos s)
    (thirdOrderConstant_neg h0 h1)
  have hm := thirdOrderMiddle_nonneg h0 h1
  unfold thirdOrderThreshold
  exact div_pos (by linarith) (by linarith [thirdOrderLeading_pos s])

/-- The sign of `T'''` on the left half is the sign of the comparison of the
logistic variable with the threshold. -/
theorem iteratedDeriv_three_smoothTransition_sign_iff (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    0 < iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) ↔
      thirdOrderThreshold s < 1 - 2 * Real.smoothTransition ((1 - s) / 2) := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hpow : (0 : ℝ) < (1 - s ^ 2) ^ 6 := pow_pos hs2 6
  have hT0 : 0 < Real.smoothTransition ((1 - s) / 2) :=
    Real.smoothTransition.pos_of_pos (by linarith)
  have hT1 : Real.smoothTransition ((1 - s) / 2) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by linarith)
  have hprod : (0 : ℝ) <
      Real.smoothTransition ((1 - s) / 2) * (1 - Real.smoothTransition ((1 - s) / 2)) :=
    mul_pos hT0 (by linarith)
  have h64 : (0 : ℝ) < 64 *
      (Real.smoothTransition ((1 - s) / 2) * (1 - Real.smoothTransition ((1 - s) / 2))) :=
    mul_pos (by norm_num) hprod
  have hu : (0 : ℝ) < 1 - 2 * Real.smoothTransition ((1 - s) / 2) :=
    one_sub_two_mul_smoothTransition_reflect_pos s h0 h1
  have hfac := iteratedDeriv_three_smoothTransition_eq_bracket s h0 h1
  have hsig : 0 < iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) ↔
      0 < thirdOrderBracket s (1 - 2 * Real.smoothTransition ((1 - s) / 2)) := by
    rw [← (mul_pos_iff_of_pos_left hpow), hfac, mul_pos_iff_of_pos_left h64]
  rw [hsig, thirdOrderBracket_eq_quadratic, thirdOrderThreshold]
  exact quadratic_pos_iff (a := thirdOrderLeading s) (b := thirdOrderMiddle s)
    (c := thirdOrderConstant s) (u := 1 - 2 * Real.smoothTransition ((1 - s) / 2))
    (thirdOrderLeading_pos s) (thirdOrderConstant_neg h0.le h1.le) hu

/-- The negative counterpart: `T''' < 0` exactly when the logistic variable is
below the threshold. -/
theorem iteratedDeriv_three_smoothTransition_neg_iff (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) < 0 ↔
      1 - 2 * Real.smoothTransition ((1 - s) / 2) < thirdOrderThreshold s := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hpow : (0 : ℝ) < (1 - s ^ 2) ^ 6 := pow_pos hs2 6
  have hT0 : 0 < Real.smoothTransition ((1 - s) / 2) :=
    Real.smoothTransition.pos_of_pos (by linarith)
  have hT1 : Real.smoothTransition ((1 - s) / 2) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by linarith)
  have hprod : (0 : ℝ) <
      Real.smoothTransition ((1 - s) / 2) * (1 - Real.smoothTransition ((1 - s) / 2)) :=
    mul_pos hT0 (by linarith)
  have h64 : (0 : ℝ) < 64 *
      (Real.smoothTransition ((1 - s) / 2) * (1 - Real.smoothTransition ((1 - s) / 2))) :=
    mul_pos (by norm_num) hprod
  have hu : (0 : ℝ) < 1 - 2 * Real.smoothTransition ((1 - s) / 2) :=
    one_sub_two_mul_smoothTransition_reflect_pos s h0 h1
  have hfac := iteratedDeriv_three_smoothTransition_eq_bracket s h0 h1
  have hscale : (1 - s ^ 2) ^ 6 * iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) < 0 ↔
      iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) < 0 :=
    mul_neg_of_pos_left_iff ((1 - s ^ 2) ^ 6)
      (iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2)) hpow
  have hprod' : 64 * (Real.smoothTransition ((1 - s) / 2) *
        (1 - Real.smoothTransition ((1 - s) / 2))) *
        thirdOrderBracket s (1 - 2 * Real.smoothTransition ((1 - s) / 2)) < 0 ↔
      thirdOrderBracket s (1 - 2 * Real.smoothTransition ((1 - s) / 2)) < 0 :=
    mul_neg_of_pos_left_iff (64 * (Real.smoothTransition ((1 - s) / 2) *
        (1 - Real.smoothTransition ((1 - s) / 2))))
      (thirdOrderBracket s (1 - 2 * Real.smoothTransition ((1 - s) / 2))) h64
  have hsig : iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) < 0 ↔
      thirdOrderBracket s (1 - 2 * Real.smoothTransition ((1 - s) / 2)) < 0 := by
    rw [← hscale, hfac, hprod']
  rw [hsig, thirdOrderBracket_eq_quadratic, thirdOrderThreshold]
  exact quadratic_neg_iff (a := thirdOrderLeading s) (b := thirdOrderMiddle s)
    (c := thirdOrderConstant s) (u := 1 - 2 * Real.smoothTransition ((1 - s) / 2))
    (thirdOrderLeading_pos s) (thirdOrderConstant_neg h0.le h1.le) hu

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
