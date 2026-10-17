/-
Record 2728, brick 1 of the reopened row-B pins campaign: the exact seed
mass `l1Mass smoothSeed = 3`.

The record-2725 tie made the mass premise `l1Mass smoothSeed <= l1u`
load-bearing at `l1u = 3` (the committed `smoothSeed_l1Mass_le_four` is
too weak: `l1u = 4` fails the wired pins 10.57x / 7.44x).  The committed
bound is the crude `||seed|| <= 1` on `[-2, 2]`; the exact value is 3, by
the flat-transition support decomposition: with `T = Real.smoothTransition`,
`T u = 1` for `u >= 1`, `T u = 0` for `u <= 0`, and
`T (1 - u) = 1 - T u` gives `int_0^1 T = 1/2`; hence
`l1Mass smoothSeed = int_0^1 T + 2 + int_0^1 T = 3`.

This is the `h1` premise of the record-2725 envelope brick
`norm_cardinalSum_poweredSeed_le_endpoint_env` at `l1u = 3`.  No producer
GO, no RH claim; the D-ladder brick (order 4 only, per record 2727) is
separate.
-/
import ConnesWeilRH.Dev.C1ExplicitSmoothSeed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction.CompactLogTest

noncomputable section

/-! ## The flat-transition symmetries -/

/-- The flat transition is symmetric about its midpoint: `T x + T (1 - x) = 1`
(both terms are `g x / (g x + g (1 - x))` and `g (1 - x) / (g (1 - x) + g x)`
for the glue `g = expNegInvGlue`, whose sum is positive everywhere). -/
theorem smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  rw [show (1 : ℝ) - (1 - x) = x by ring]
  have hden :
      expNegInvGlue (1 - x) / (expNegInvGlue (1 - x) + expNegInvGlue x) =
        expNegInvGlue (1 - x) / (expNegInvGlue x + expNegInvGlue (1 - x)) := by
    rw [add_comm]
  rw [hden, ← add_div, div_self (Real.smoothTransition.pos_denom x).ne']

/-- The midpoint reflection of the flat transition. -/
theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  have h := smoothTransition_add_one_sub x
  linarith

/-- `∫_0^1 T = 1/2`: the substitution `u ↦ 1 - u` fixes the interval and
turns the integrand into `1 - T`, so the integral equals `1` minus itself. -/
theorem integral_smoothTransition_zero_one :
    ∫ x in (0 : ℝ)..1, Real.smoothTransition x = 1 / 2 := by
  have hT : IntervalIntegrable Real.smoothTransition volume (0 : ℝ) 1 :=
    Real.smoothTransition.continuous.intervalIntegrable 0 1
  have h1 : (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x)) =
      ∫ x in (0 : ℝ)..1, Real.smoothTransition x := by
    rw [intervalIntegral.integral_comp_sub_left Real.smoothTransition 1]
    norm_num
  have h2 : (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x)) =
      ∫ x in (0 : ℝ)..1, (1 - Real.smoothTransition x) :=
    intervalIntegral.integral_congr fun x _ => smoothTransition_one_sub x
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1 :=
    continuous_const.intervalIntegrable 0 1
  have h3 : (∫ x in (0 : ℝ)..1, (1 - Real.smoothTransition x)) =
      1 - ∫ x in (0 : ℝ)..1, Real.smoothTransition x := by
    have h := intervalIntegral.integral_sub
      (f := fun _ : ℝ => (1 : ℝ)) (g := Real.smoothTransition) hc hT
    simpa using h
  have hchain : (∫ x in (0 : ℝ)..1, Real.smoothTransition x) =
      1 - ∫ x in (0 : ℝ)..1, Real.smoothTransition x :=
    calc ∫ x in (0 : ℝ)..1, Real.smoothTransition x
        = ∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x) := h1.symm
      _ = ∫ x in (0 : ℝ)..1, (1 - Real.smoothTransition x) := h2
      _ = 1 - ∫ x in (0 : ℝ)..1, Real.smoothTransition x := h3
  linarith

/-! ## The exact seed mass -/

theorem norm_smoothSeed_test_eq (x : ℝ) :
    ‖smoothSeed.test x‖ = smoothSeedRaw x := by
  simpa only [smoothSeed_apply, smoothSeedComplex,
    abs_of_nonneg (smoothSeedRaw_nonneg x)] using
    RCLike.norm_ofReal (K := ℂ) (smoothSeedRaw x)

theorem smoothSeedRaw_eq_zero_of_notMem_Icc {x : ℝ}
    (hx : x ∉ Set.Icc (-2 : ℝ) 2) : smoothSeedRaw x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with h | h
  · exact smoothSeedRaw_eq_zero_of_le (le_of_lt (not_le.mp h))
  · exact smoothSeedRaw_eq_zero_of_ge (le_of_lt (not_le.mp h))

/-- The exact value of the seed's `L¹` mass: `3`. -/
theorem integral_smoothSeedRaw_eq_three : ∫ x : ℝ, smoothSeedRaw x = 3 := by
  have h1 : (∫ x : ℝ, smoothSeedRaw x) =
      ∫ x, (Set.Icc (-2 : ℝ) 2).indicator smoothSeedRaw x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (-2 : ℝ) 2
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, smoothSeedRaw_eq_zero_of_notMem_Icc hx]
  have h2 : (∫ x, (Set.Icc (-2 : ℝ) 2).indicator smoothSeedRaw x) =
      ∫ x in (-2 : ℝ)..2, smoothSeedRaw x := by
    rw [integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le (show (-2 : ℝ) ≤ 2 by norm_num)).symm
  have hint : ∀ a b : ℝ, IntervalIntegrable smoothSeedRaw volume a b :=
    fun a b => smoothSeedRaw_contDiff.continuous.intervalIntegrable a b
  have h12 : (∫ x in (-2 : ℝ)..2, smoothSeedRaw x) =
      (∫ x in (-2 : ℝ)..(-1), smoothSeedRaw x) +
        ∫ x in (-1 : ℝ)..2, smoothSeedRaw x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (f := smoothSeedRaw) (hint _ _) (hint _ _)).symm
  have h23 : (∫ x in (-1 : ℝ)..2, smoothSeedRaw x) =
      (∫ x in (-1 : ℝ)..1, smoothSeedRaw x) +
        ∫ x in (1 : ℝ)..2, smoothSeedRaw x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (f := smoothSeedRaw) (hint _ _) (hint _ _)).symm
  have hleft : (∫ x in (-2 : ℝ)..(-1), smoothSeedRaw x) = 1 / 2 := by
    have hpt : ∀ x ∈ Set.uIcc (-2 : ℝ) (-1),
        smoothSeedRaw x = Real.smoothTransition (x + 2) := by
      intro x hx
      have hxle : x ≤ -1 := by
        have hmem : x ∈ Set.Icc (-2 : ℝ) (-1) := by
          simpa [Set.uIcc_of_le (show (-2 : ℝ) ≤ -1 by norm_num)] using hx
        exact hmem.2
      unfold smoothSeedRaw
      rw [Real.smoothTransition.one_of_one_le
        (show (1 : ℝ) ≤ 2 - x by linarith), mul_one]
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_comp_add_right Real.smoothTransition 2]
    norm_num
    exact integral_smoothTransition_zero_one
  have hright : (∫ x in (1 : ℝ)..2, smoothSeedRaw x) = 1 / 2 := by
    have hpt : ∀ x ∈ Set.uIcc (1 : ℝ) 2,
        smoothSeedRaw x = Real.smoothTransition (2 - x) := by
      intro x hx
      have hxge : 1 ≤ x := by
        have hmem : x ∈ Set.Icc (1 : ℝ) 2 := by
          simpa [Set.uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hx
        exact hmem.1
      unfold smoothSeedRaw
      rw [Real.smoothTransition.one_of_one_le
        (show (1 : ℝ) ≤ x + 2 by linarith), one_mul]
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_comp_sub_left Real.smoothTransition 2]
    norm_num
    exact integral_smoothTransition_zero_one
  have hmid : (∫ x in (-1 : ℝ)..1, smoothSeedRaw x) = 2 := by
    have hpt : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, smoothSeedRaw x = 1 := by
      intro x hx
      have hmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using hx
      exact smoothSeedRaw_eq_one_of_mem_Icc hmem
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  calc ∫ x : ℝ, smoothSeedRaw x
      = ∫ x, (Set.Icc (-2 : ℝ) 2).indicator smoothSeedRaw x := h1
    _ = ∫ x in (-2 : ℝ)..2, smoothSeedRaw x := h2
    _ = (∫ x in (-2 : ℝ)..(-1), smoothSeedRaw x) +
          ∫ x in (-1 : ℝ)..2, smoothSeedRaw x := h12
    _ = (∫ x in (-2 : ℝ)..(-1), smoothSeedRaw x) +
          ((∫ x in (-1 : ℝ)..1, smoothSeedRaw x) +
            ∫ x in (1 : ℝ)..2, smoothSeedRaw x) := by
        rw [h23]
    _ = 1 / 2 + (2 + 1 / 2) := by rw [hleft, hmid, hright]
    _ = 3 := by norm_num

/-- The load-bearing mass premise at `l1u = 3` (record 2725). -/
theorem l1Mass_smoothSeed_eq_three : l1Mass smoothSeed = 3 := by
  calc l1Mass smoothSeed
      = ∫ x : ℝ, ‖smoothSeed.test x‖ := rfl
    _ = ∫ x : ℝ, smoothSeedRaw x := by
        apply integral_congr_ae
        filter_upwards with x
        exact norm_smoothSeed_test_eq x
    _ = 3 := integral_smoothSeedRaw_eq_three

/-- The envelope-brick premise in the exact shape record 2725 consumes. -/
theorem smoothSeed_l1Mass_le_three : l1Mass smoothSeed ≤ 3 :=
  le_of_eq l1Mass_smoothSeed_eq_three

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
