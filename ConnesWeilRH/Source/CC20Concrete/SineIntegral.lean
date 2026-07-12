/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The sine integral used by the regular CC20 kernel

The singular distributional part of `Q delta` must be separated from its
ordinary regular kernel.  This file records the elementary analytic function
that occurs in the regular part.  It intentionally does not assert a kernel
action or a Hilbert--Schmidt estimate; those are separate source obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open Filter
open scoped Topology
open scoped Interval

/-- The (unnormalized) sine integral, defined as an oriented interval integral. -/
noncomputable def sineIntegral (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.sinc t

@[simp]
theorem sineIntegral_zero : sineIntegral 0 = 0 := by
  simp [sineIntegral]

@[fun_prop, continuity]
theorem continuous_sineIntegral : Continuous sineIntegral := by
  unfold sineIntegral
  exact intervalIntegral.continuous_primitive
    (fun a b => Real.continuous_sinc.intervalIntegrable a b) 0

@[fun_prop]
theorem measurable_sineIntegral : Measurable sineIntegral :=
  continuous_sineIntegral.measurable

theorem deriv_sineIntegral (x : ℝ) :
    deriv sineIntegral x = Real.sinc x := by
  unfold sineIntegral
  exact Continuous.deriv_integral Real.sinc Real.continuous_sinc 0 x

theorem hasDerivAt_sineIntegral (x : ℝ) :
    HasDerivAt sineIntegral (Real.sinc x) x := by
  unfold sineIntegral
  exact (Real.continuous_sinc.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem sineIntegral_intervalIntegral (a b : ℝ) :
    ∫ t in a..b, Real.sinc t = sineIntegral b - sineIntegral a := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (f := Real.sinc) (μ := volume)
    (Real.continuous_sinc.intervalIntegrable 0 a)
    (Real.continuous_sinc.intervalIntegrable a b)
  dsimp [sineIntegral]
  linarith

/-- Continuous extension of `sineIntegral x / x` at the origin.

The integral-average definition is useful because it has no removable
singularity in its Lean representation. -/
noncomputable def sineIntegralQuotient (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sinc (x * t)

@[simp]
theorem sineIntegralQuotient_zero : sineIntegralQuotient 0 = 1 := by
  simp [sineIntegralQuotient]

@[fun_prop, continuity]
theorem continuous_sineIntegralQuotient : Continuous sineIntegralQuotient := by
  unfold sineIntegralQuotient
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

@[fun_prop]
theorem measurable_sineIntegralQuotient : Measurable sineIntegralQuotient :=
  continuous_sineIntegralQuotient.measurable

lemma sinc_slope_bound_pos {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |(Real.sinc x - 1) / x| ≤ x / 4 := by
  have hsin_upper : Real.sin x < x := Real.sin_lt hx
  have hsin_lower : x - x ^ 3 / 4 < Real.sin x :=
    Real.sin_gt_sub_cube hx hx1
  have hdiff : |Real.sin x - x| ≤ x ^ 3 / 4 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [Real.sinc_of_ne_zero hx.ne']
  have hinner : (Real.sin x / x - 1) / x =
      (Real.sin x - x) / x ^ 2 := by
    field_simp [hx.ne']
  rw [hinner, abs_div, abs_of_pos (sq_pos_of_pos hx)]
  calc
    |Real.sin x - x| / x ^ 2 ≤ (x ^ 3 / 4) / x ^ 2 := by
      gcongr
    _ = x / 4 := by field_simp [hx.ne']

lemma sinc_slope_bound_neg {x : ℝ} (hx : -1 ≤ x) (hx0 : x < 0) :
    |(Real.sinc x - 1) / x| ≤ (-x) / 4 := by
  have hy : 0 < -x := neg_pos.mpr hx0
  have hy1 : -x ≤ 1 := by linarith
  have h := sinc_slope_bound_pos hy hy1
  simpa [Real.sinc_neg, abs_neg, div_neg] using h

lemma sinc_diff_bound_unit {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sinc x - 1| ≤ x ^ 2 / 4 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · have hs := sinc_slope_bound_neg (abs_le.mp hx).1 hxneg
    have hmul : |(Real.sinc x - 1) / x| * (-x) ≤ ((-x) / 4) * (-x) :=
      mul_le_mul_of_nonneg_right hs (le_of_lt (neg_pos.mpr hxneg))
    have heq : |Real.sinc x - 1| =
        |(Real.sinc x - 1) / x| * (-x) := by
      rw [abs_div, abs_of_neg hxneg]
      field_simp [ne_of_lt hxneg]
    rw [heq] at *
    nlinarith [sq_nonneg x]
  · have hs := sinc_slope_bound_pos hxpos (abs_le.mp hx).2
    have hmul : |(Real.sinc x - 1) / x| * x ≤ (x / 4) * x :=
      mul_le_mul_of_nonneg_right hs (le_of_lt hxpos)
    have heq : |Real.sinc x - 1| =
        |(Real.sinc x - 1) / x| * x := by
      rw [abs_div, abs_of_pos hxpos]
      field_simp [ne_of_gt hxpos]
    rw [heq] at *
    nlinarith [sq_nonneg x]

lemma sineIntegralQuotient_sub_one_bound {x : ℝ} (hx : |x| ≤ 1) :
    |sineIntegralQuotient x - 1| ≤ x ^ 2 / 4 := by
  have hint : IntervalIntegrable (fun t : ℝ => Real.sinc (x * t) - 1)
      volume 0 1 := by
    exact ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).sub
      continuous_const).intervalIntegrable 0 1
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      |Real.sinc (x * t) - 1| ≤ x ^ 2 / 4 := by
    intro t ht
    have ht0 : 0 ≤ t := by simpa [Set.uIoc] using ht.1.le
    have ht1 : t ≤ 1 := by simpa [Set.uIoc] using ht.2
    have hxt : |x * t| ≤ 1 := by
      rw [abs_mul]
      have htabs : |t| ≤ 1 := by simpa [abs_of_nonneg ht0] using ht1
      nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg t),
        mul_le_mul hx htabs (abs_nonneg t) (by positivity)]
    have h := sinc_diff_bound_unit hxt
    have htsq : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    have hprod := mul_le_mul_of_nonneg_left htsq (sq_nonneg x)
    nlinarith [hprod]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => Real.sinc (x * t) - 1) (a := (0 : ℝ)) (b := 1)
    (C := x ^ 2 / 4) (by simpa [Real.norm_eq_abs] using hbound)
  have hrew : sineIntegralQuotient x - 1 =
      ∫ t in (0 : ℝ)..1, (Real.sinc (x * t) - 1) := by
    simpa [sineIntegralQuotient] using
      (intervalIntegral.integral_sub
        (f := fun t : ℝ => Real.sinc (x * t))
        (g := fun _ : ℝ => (1 : ℝ))
        ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).intervalIntegrable
          (μ := volume) 0 1)
        (continuous_const.intervalIntegrable (μ := volume) 0 1)).symm
  rw [hrew]
  simpa using hnorm

theorem hasDerivAt_sineIntegralQuotient_zero :
    HasDerivAt sineIntegralQuotient 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 := by
    have hlt : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < 1 := by
      exact (continuous_abs.continuousAt : ContinuousAt (fun t : ℝ => |t|) 0).eventually_lt
        continuousAt_const (by norm_num)
    filter_upwards [hlt.filter_mono nhdsWithin_le_nhds] with t ht
    exact le_of_lt ht
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ‖t⁻¹ * (sineIntegralQuotient (0 + t) - sineIntegralQuotient 0)‖ ≤ |t| / 4 := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht hne
    have hq := sineIntegralQuotient_sub_one_bound ht
    simp only [zero_add, sineIntegralQuotient_zero]
    rw [Real.norm_eq_abs, abs_mul, abs_inv]
    have htnz : t ≠ 0 := hne
    have habsnz : |t| ≠ 0 := abs_ne_zero.mpr htnz
    calc
      |t|⁻¹ * |sineIntegralQuotient t - 1| ≤ |t|⁻¹ * (t ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr (abs_nonneg t))
      _ = |t| / 4 := by
        rw [← sq_abs]
        field_simp [habsnz]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hbound
  have habs : Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    by simpa using
      ((continuous_abs.continuousAt : ContinuousAt (fun t : ℝ => |t|) 0).tendsto.mono_left
        nhdsWithin_le_nhds)
  simpa using habs.div_const 4

theorem hasDerivAt_sinc_zero : HasDerivAt Real.sinc 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · rw [slope_fun_def_field]
    simp only [zero_add, Real.sinc_zero, sub_zero]
    have hsmall : ∀ᶠ t in 𝓝[<] (0 : ℝ), -1 < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (continuousAt_const.eventually_lt continuousAt_id (by norm_num))
    have hbound : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        |(Real.sinc t - 1) / t| ≤ (-t) / 4 := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
      exact sinc_slope_bound_neg (le_of_lt ht1) ht
    have hleft : Tendsto (fun t : ℝ => t / 4) (𝓝[<] 0) (𝓝 0) := by
      simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => t / 4) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0))
    have hright : Tendsto (fun t : ℝ => (-t) / 4) (𝓝[<] 0) (𝓝 0) := by
      simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => (-t) / 4) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0))
    have hlow : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        t / 4 ≤ (Real.sinc t - 1) / t := by
      filter_upwards [hbound] with t ht
      simpa [neg_div] using (abs_le.mp ht).1
    have hupp : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        (Real.sinc t - 1) / t ≤ (-t) / 4 := by
      filter_upwards [hbound] with t ht
      exact (abs_le.mp ht).2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright hlow hupp
  · rw [slope_fun_def_field]
    simp only [zero_add, Real.sinc_zero, sub_zero]
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (continuousAt_id.eventually_lt continuousAt_const (by norm_num))
    have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |(Real.sinc t - 1) / t| ≤ t / 4 := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
      exact sinc_slope_bound_pos ht (le_of_lt ht1)
    have hleft : Tendsto (fun t : ℝ => (-t) / 4) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => (-t) / 4) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    have hright : Tendsto (fun t : ℝ => t / 4) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => t / 4) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    have hlow : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (-t) / 4 ≤ (Real.sinc t - 1) / t := by
      filter_upwards [hbound] with t ht
      simpa [neg_div] using (abs_le.mp ht).1
    have hupp : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (Real.sinc t - 1) / t ≤ t / 4 := by
      filter_upwards [hbound] with t ht
      exact (abs_le.mp ht).2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright hlow hupp

theorem sineIntegralQuotient_eq_div (x : ℝ) (hx : x ≠ 0) :
    sineIntegralQuotient x = sineIntegral x / x := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := Real.sinc) x (a := (0 : ℝ)) (b := 1)
  have h' : x * sineIntegralQuotient x = sineIntegral x := by
    simpa [sineIntegralQuotient, sineIntegral, smul_eq_mul] using h
  exact (eq_div_iff hx).2 (by simpa [mul_comm] using h')

theorem hasDerivAt_sineIntegralQuotient (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt sineIntegralQuotient
      ((Real.sinc x * x - sineIntegral x) / x ^ 2) x := by
  have hsi : HasDerivAt sineIntegral (Real.sinc x) x := by
    unfold sineIntegral
    exact (Real.continuous_sinc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hdiv : HasDerivAt (fun y : ℝ => sineIntegral y / y)
      ((Real.sinc x * x - sineIntegral x) / x ^ 2) x := by
    simpa using hsi.div (hasDerivAt_id x) hx
  have hlocal : sineIntegralQuotient =ᶠ[𝓝 x]
      (fun y : ℝ => sineIntegral y / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact sineIntegralQuotient_eq_div y hy
  exact hdiv.congr_of_eventuallyEq hlocal

theorem deriv_sineIntegralQuotient (x : ℝ) (hx : x ≠ 0) :
    deriv sineIntegralQuotient x =
      (Real.sinc x * x - sineIntegral x) / x ^ 2 :=
  (hasDerivAt_sineIntegralQuotient x hx).deriv

theorem hasDerivAt_sinc_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Real.sinc ((Real.cos x * x - Real.sin x) / x ^ 2) x := by
  have hdiv : HasDerivAt (fun y : ℝ => Real.sin y / y)
      ((Real.cos x * x - Real.sin x) / x ^ 2) x := by
    simpa using (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have hlocal : Real.sinc =ᶠ[𝓝 x] (fun y : ℝ => Real.sin y / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact Real.sinc_of_ne_zero hy
  exact hdiv.congr_of_eventuallyEq hlocal

theorem deriv_sinc_zero : deriv Real.sinc 0 = 0 :=
  hasDerivAt_sinc_zero.deriv

theorem tendsto_sinc_derivative_slope_zero :
    Tendsto (fun x : ℝ => (Real.cos x * x - Real.sin x) / x ^ 3)
      (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) := by
  have hnumDeriv : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun y : ℝ => Real.cos y * y - Real.sin y)
        (-x * Real.sin x) x := by
    filter_upwards [] with x
    convert ((Real.hasDerivAt_cos x).mul (hasDerivAt_id' x)).sub
      (Real.hasDerivAt_sin x) using 1 <;> ring
  have hdenDeriv : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    filter_upwards [] with x
    convert (hasDerivAt_id' x).pow 3 using 1 <;> ring
  have hdenNe : ∀ᶠ x : ℝ in 𝓝[≠] 0, 3 * x ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have hnumZero : Tendsto (fun x : ℝ => Real.cos x * x - Real.sin x)
      (𝓝[≠] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.cos x * x - Real.sin x) 0 :=
      ((Real.continuous_cos.mul continuous_id).sub Real.continuous_sin).continuousAt
    simpa using hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hdenZero : Tendsto (fun x : ℝ => x ^ 3) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuousAt_id.pow 3).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hsinc : Tendsto (fun x : ℝ => -Real.sinc x / 3)
      (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) := by
    simpa using (Real.continuous_sinc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).neg.div_const 3
  have hratio : Tendsto (fun x : ℝ => (-x * Real.sin x) / (3 * x ^ 2))
      (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) := by
    apply hsinc.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.sinc_of_ne_zero hx]
    field_simp [hx]
  exact HasDerivAt.lhopital_zero_nhdsNE hnumDeriv hdenDeriv hdenNe
    hnumZero hdenZero hratio

theorem hasDerivAt_deriv_sinc_zero :
    HasDerivAt (deriv Real.sinc) (-1 / 3) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim := tendsto_sinc_derivative_slope_zero
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [zero_add, deriv_sinc_zero, sub_zero,
    (hasDerivAt_sinc_of_ne_zero x hx).deriv]
  simp only [smul_eq_mul]
  field_simp [hx]

noncomputable def sineIntegralQuotientSecondDerivativeProfile (x : ℝ) : ℝ :=
  ((((Real.cos x * x - Real.sin x) / x ^ 2) * x + Real.sinc x - Real.sinc x) * x ^ 2 -
      (Real.sinc x * x - sineIntegral x) * (2 * x)) / (x ^ 2) ^ 2

@[simp]
theorem siQuotientDerivativeProfile_zero :
    (Real.sinc 0 * 0 - sineIntegral 0) / (0 : ℝ) ^ 2 = 0 := by simp

theorem hasDerivAt_sineIntegralQuotient_all (x : ℝ) :
    HasDerivAt sineIntegralQuotient
      ((Real.sinc x * x - sineIntegral x) / x ^ 2) x := by
  by_cases hx : x = 0
  · subst x
    simpa using hasDerivAt_sineIntegralQuotient_zero
  · exact hasDerivAt_sineIntegralQuotient x hx

theorem deriv_sineIntegralQuotient_all (x : ℝ) :
    deriv sineIntegralQuotient x =
      (Real.sinc x * x - sineIntegral x) / x ^ 2 :=
  (hasDerivAt_sineIntegralQuotient_all x).deriv

theorem tendsto_siQuotientDerivative_slope_zero :
    Tendsto (fun x : ℝ => (Real.sin x - sineIntegral x) / x ^ 3)
      (𝓝[≠] 0) (𝓝 (-1 / 9 : ℝ)) := by
  have hfirstNumDeriv : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun y : ℝ => Real.sin y - sineIntegral y)
        (Real.cos x - Real.sinc x) x := by
    filter_upwards [] with x
    exact (Real.hasDerivAt_sin x).sub (hasDerivAt_sineIntegral x)
  have hfirstDenDeriv : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    filter_upwards [] with x
    convert (hasDerivAt_id' x).pow 3 using 1 <;> ring
  have hfirstDenNe : ∀ᶠ x : ℝ in 𝓝[≠] 0, 3 * x ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have hfirstNumZero : Tendsto (fun x : ℝ => Real.sin x - sineIntegral x)
      (𝓝[≠] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.sin x - sineIntegral x) 0 :=
      Real.continuous_sin.continuousAt.sub continuous_sineIntegral.continuousAt
    simpa using hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hfirstDenZero : Tendsto (fun x : ℝ => x ^ 3) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuousAt_id.pow 3).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hsecondNumDeriv : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun y : ℝ => Real.cos y - Real.sinc y)
        (-Real.sin x - deriv Real.sinc x) x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsinc := hasDerivAt_sinc_of_ne_zero x hx
    convert (Real.hasDerivAt_cos x).sub hsinc using 1
    rw [hsinc.deriv]
  have hsecondDenDeriv : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
    filter_upwards [] with x
    convert ((hasDerivAt_id' x).pow 2).const_mul 3 using 1 <;> ring
  have hsecondDenNe : ∀ᶠ x : ℝ in 𝓝[≠] 0, 6 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) hx
  have hsecondNumZero : Tendsto (fun x : ℝ => Real.cos x - Real.sinc x)
      (𝓝[≠] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.cos x - Real.sinc x) 0 :=
      Real.continuous_cos.continuousAt.sub Real.continuous_sinc.continuousAt
    simpa using hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hsecondDenZero : Tendsto (fun x : ℝ => 3 * x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuousAt_const.mul (continuousAt_id.pow 2)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hfinalDerivative : HasDerivAt
      (fun x : ℝ => -Real.sin x - deriv Real.sinc x) (-2 / 3) 0 := by
    convert (Real.hasDerivAt_sin 0).neg.sub hasDerivAt_deriv_sinc_zero using 1 <;>
      norm_num [deriv_sinc_zero]
  have hfinalRatio : Tendsto
      (fun x : ℝ => (-Real.sin x - deriv Real.sinc x) / (6 * x))
      (𝓝[≠] 0) (𝓝 (-1 / 9 : ℝ)) := by
    have hslope := hfinalDerivative.tendsto_slope_zero
    have hslope' : Tendsto
        (fun x : ℝ => (-Real.sin x - deriv Real.sinc x) / x)
        (𝓝[≠] 0) (𝓝 (-2 / 3 : ℝ)) := by
      simpa [deriv_sinc_zero, smul_eq_mul, div_eq_inv_mul, mul_comm] using hslope
    convert hslope'.div_const 6 using 1
    · funext x
      simp [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
    · norm_num
  have hsecondRatio : Tendsto
      (fun x : ℝ => (Real.cos x - Real.sinc x) / (3 * x ^ 2))
      (𝓝[≠] 0) (𝓝 (-1 / 9 : ℝ)) :=
    HasDerivAt.lhopital_zero_nhdsNE hsecondNumDeriv hsecondDenDeriv hsecondDenNe
      hsecondNumZero hsecondDenZero hfinalRatio
  exact HasDerivAt.lhopital_zero_nhdsNE hfirstNumDeriv hfirstDenDeriv hfirstDenNe
    hfirstNumZero hfirstDenZero hsecondRatio

theorem hasDerivAt_siQuotientDerivativeProfile_zero :
    HasDerivAt
      (fun x : ℝ => (Real.sinc x * x - sineIntegral x) / x ^ 2)
      (-1 / 9) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim := tendsto_siQuotientDerivative_slope_zero
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [zero_add]
  have hzero : (Real.sinc 0 * 0 - sineIntegral 0) / (0 : ℝ) ^ 2 = 0 := by
    simp
  rw [hzero, sub_zero]
  simp only [smul_eq_mul]
  rw [Real.sinc_of_ne_zero hx]
  rw [div_mul_cancel₀ _ hx]
  field_simp [hx]

theorem hasDerivAt_deriv_sineIntegralQuotient_zero :
    HasDerivAt (deriv sineIntegralQuotient) (-1 / 9) 0 := by
  have hprofile := hasDerivAt_siQuotientDerivativeProfile_zero
  have heq : deriv sineIntegralQuotient =
      fun x : ℝ => (Real.sinc x * x - sineIntegral x) / x ^ 2 := by
    funext x
    exact deriv_sineIntegralQuotient_all x
  simpa [heq] using hprofile

theorem tendsto_sineIntegralQuotientSecondDerivativeProfile_zero :
    Tendsto sineIntegralQuotientSecondDerivativeProfile
      (𝓝[≠] 0) (𝓝 (-1 / 9 : ℝ)) := by
  have hcombined := tendsto_sinc_derivative_slope_zero.sub
    (tendsto_siQuotientDerivative_slope_zero.const_mul 2)
  have htarget : Tendsto
      (fun x : ℝ =>
        (Real.cos x * x - Real.sin x) / x ^ 3 -
          2 * ((Real.sin x - sineIntegral x) / x ^ 3))
      (𝓝[≠] 0) (𝓝 (-1 / 9 : ℝ)) := by
    convert hcombined using 1 <;> norm_num
  apply htarget.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  unfold sineIntegralQuotientSecondDerivativeProfile
  rw [Real.sinc_of_ne_zero hx0]
  field_simp [hx0]
  ring

/-- Continuous repair of the explicit second-derivative formula at its
removable singularity. -/
noncomputable def sineIntegralQuotientSecondDerivativeExtension (x : ℝ) : ℝ :=
  Function.update sineIntegralQuotientSecondDerivativeProfile 0 (-1 / 9) x

@[simp]
theorem sineIntegralQuotientSecondDerivativeExtension_zero :
    sineIntegralQuotientSecondDerivativeExtension 0 = -1 / 9 := by
  simp [sineIntegralQuotientSecondDerivativeExtension]

theorem sineIntegralQuotientSecondDerivativeExtension_of_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    sineIntegralQuotientSecondDerivativeExtension x =
      sineIntegralQuotientSecondDerivativeProfile x := by
  simp [sineIntegralQuotientSecondDerivativeExtension, hx]

@[fun_prop, continuity]
theorem continuous_sineIntegralQuotientSecondDerivativeExtension :
    Continuous sineIntegralQuotientSecondDerivativeExtension := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_update_same.mpr
      tendsto_sineIntegralQuotientSecondDerivativeProfile_zero
  · change ContinuousAt
      (Function.update sineIntegralQuotientSecondDerivativeProfile 0 (-1 / 9)) x
    rw [continuousAt_update_of_ne hx]
    unfold sineIntegralQuotientSecondDerivativeProfile
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hcos : ContinuousAt Real.cos x := Real.continuous_cos.continuousAt
    have hsin : ContinuousAt Real.sin x := Real.continuous_sin.continuousAt
    have hsinc : ContinuousAt Real.sinc x := Real.continuous_sinc.continuousAt
    have hsi : ContinuousAt sineIntegral x := continuous_sineIntegral.continuousAt
    have hquot : ContinuousAt
        (fun y : ℝ => (Real.cos y * y - Real.sin y) / y ^ 2) x :=
      ((hcos.mul continuousAt_id).sub hsin).div (continuousAt_id.pow 2) hx2
    exact (((((hquot.mul continuousAt_id).add hsinc).sub hsinc).mul
      (continuousAt_id.pow 2)).sub
        (((hsinc.mul continuousAt_id).sub hsi).mul
          (continuousAt_const.mul continuousAt_id))).div
      ((continuousAt_id.pow 2).pow 2) (pow_ne_zero 2 hx2)

@[continuity, fun_prop]
theorem continuousAt_sineIntegralQuotientSecondDerivativeProfile_of_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt sineIntegralQuotientSecondDerivativeProfile x := by
  unfold sineIntegralQuotientSecondDerivativeProfile
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hcos : ContinuousAt Real.cos x := Real.continuous_cos.continuousAt
  have hsin : ContinuousAt Real.sin x := Real.continuous_sin.continuousAt
  have hsinc : ContinuousAt Real.sinc x := Real.continuous_sinc.continuousAt
  have hsi : ContinuousAt sineIntegral x := continuous_sineIntegral.continuousAt
  have hquot : ContinuousAt
      (fun y : ℝ => (Real.cos y * y - Real.sin y) / y ^ 2) x :=
    ((hcos.mul continuousAt_id).sub hsin).div (continuousAt_id.pow 2) hx2
  exact (((((hquot.mul continuousAt_id).add hsinc).sub hsinc).mul
    (continuousAt_id.pow 2)).sub
      (((hsinc.mul continuousAt_id).sub hsi).mul
        (continuousAt_const.mul continuousAt_id))).div
    ((continuousAt_id.pow 2).pow 2) (pow_ne_zero 2 hx2)

theorem hasDerivAt_deriv_sineIntegralQuotient (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (deriv sineIntegralQuotient)
      (sineIntegralQuotientSecondDerivativeProfile x) x := by
  have hsinc := hasDerivAt_sinc_of_ne_zero x hx
  have hsi : HasDerivAt sineIntegral (Real.sinc x) x := by
    unfold sineIntegral
    exact (Real.continuous_sinc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hnum := hsinc.mul (hasDerivAt_id x)
  have hnum' := hnum.sub hsi
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_two] using (hasDerivAt_id x).pow 2
  have hquot := hnum'.div hden (pow_ne_zero 2 hx)
  have hlocal : deriv sineIntegralQuotient =ᶠ[𝓝 x]
      (fun y : ℝ => (Real.sinc y * y - sineIntegral y) / y ^ 2) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact deriv_sineIntegralQuotient y hy
  convert hquot.congr_of_eventuallyEq hlocal using 1 <;>
    simp [sineIntegralQuotientSecondDerivativeProfile] <;> ring

end CC20Concrete
end Source
end ConnesWeilRH
