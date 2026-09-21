/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3GammaRBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# C3' sigma kernel

The paper's archimedean sigma profile is the real part of the same
`Gamma_R` logarithmic derivative already used by the C3 carrier.  This leaf
records that coordinate change exactly, so a later sign certificate can be
stated on the actual Gamma_R owner rather than on an unrelated special
function expression.
-/

namespace ConnesWeilRH
namespace Dev

open Complex

noncomputable def c3Sigma (xi : Real) : Real :=
  Real.log Real.pi -
    (Complex.digamma
      (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)).re

theorem c3Sigma_zero_lt_twelve : c3Sigma 0 < 12 := by
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgamma_pos : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hdig := abs_digamma_le_of_re_ge_quarter
    (w := ((1 / 4 : Real) : Complex)) (by norm_num)
  have hhalf : ‖Complex.digamma ((1 / 2 : Real) : Complex)‖ ≤
      2 * Real.log 2 + Real.eulerMascheroniConstant := by
    rw [show ((1 / 2 : Real) : Complex) = (1 / 2 : Complex) by norm_num,
      Complex.digamma_one_half]
    have hlog2c : Complex.log (2 : Complex) = (Real.log 2 : Complex) := by
      simpa using (Complex.natCast_log (n := 2)).symm
    rw [hlog2c]
    have hnorm2 : ‖(2 * Real.log 2 : Complex)‖ = 2 * Real.log 2 := by
      calc
        ‖(2 * Real.log 2 : Complex)‖ =
            ‖(2 : Complex)‖ * ‖(Real.log 2 : Complex)‖ := by rw [norm_mul]
        _ = 2 * Real.log 2 := by
          calc
            ‖(2 : Complex)‖ * ‖(Real.log 2 : Complex)‖ =
                (2 : Real) * |Real.log 2| := by
              simp only [Complex.norm_real, Real.norm_eq_abs]
              norm_num
            _ = 2 * Real.log 2 := by rw [abs_of_nonneg hlog2nonneg]
    have hnormg : ‖(Real.eulerMascheroniConstant : Complex)‖ =
        Real.eulerMascheroniConstant := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgamma_pos.le]
    calc
      ‖-2 * (Real.log 2 : Complex) -
          (Real.eulerMascheroniConstant : Complex)‖ ≤
          ‖-(2 * Real.log 2 : Complex)‖ +
            ‖-(Real.eulerMascheroniConstant : Complex)‖ := by
        convert norm_add_le (-(2 * Real.log 2 : Complex))
          (-(Real.eulerMascheroniConstant : Complex)) using 1 <;> ring_nf
      _ = 2 * Real.log 2 + Real.eulerMascheroniConstant := by
        rw [norm_neg, norm_neg, hnorm2, hnormg]
  have hlogpi : Real.log Real.pi < 4 := by
    have hlog := Real.log_le_sub_one_of_pos Real.pi_pos
    nlinarith [Real.pi_lt_four]
  have hreal :
      -((Complex.digamma ((1 / 4 : Real) : Complex)).re) ≤
        ‖Complex.digamma ((1 / 4 : Real) : Complex)‖ := by
    exact le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
  have hreal' : -(Complex.digamma (1 / 4 : Complex)).re ≤
      ‖Complex.digamma (1 / 4 : Complex)‖ := by
    simpa only [show ((1 / 4 : Real) : Complex) = (1 / 4 : Complex) by norm_num]
      using hreal
  have hlog2 : Real.log 2 < (7 : Real) / 10 := by
    nlinarith [Real.log_two_lt_d9]
  have hgamma : Real.eulerMascheroniConstant < (2 : Real) / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hhalf' : ‖Complex.digamma (1 / 2 : Complex)‖ ≤
      2 * Real.log 2 + Real.eulerMascheroniConstant := by
    simpa only [show ((1 / 2 : Real) : Complex) = (1 / 2 : Complex) by norm_num]
      using hhalf
  have hdig' : ‖Complex.digamma ((1 / 4 : Real) : Complex)‖ ≤
      (2 * Real.log 2 + Real.eulerMascheroniConstant) + 4 + 6 / 5 + 3 / 5 := by
    calc
      ‖Complex.digamma ((1 / 4 : Real) : Complex)‖ ≤
          ‖Complex.digamma (1 / 2 : Complex)‖ + 4 + 6 / 5 +
            (12 / 5 : Real) * ‖((1 / 4 : Real) : Complex)‖ := hdig
      _ = ‖Complex.digamma (1 / 2 : Complex)‖ + 4 + 6 / 5 + 3 / 5 := by
        norm_num [Complex.norm_real]
      _ ≤ _ := by gcongr
  have hdig'' : ‖Complex.digamma (1 / 4 : Complex)‖ ≤
      (2 * Real.log 2 + Real.eulerMascheroniConstant) + 4 + 6 / 5 + 3 / 5 := by
    simpa only [show ((1 / 4 : Real) : Complex) = (1 / 4 : Complex) by norm_num]
      using hdig'
  have hbound : c3Sigma 0 ≤ Real.log Real.pi +
      (2 * Real.log 2 + Real.eulerMascheroniConstant) + 4 + 6 / 5 + 3 / 5 := by
    unfold c3Sigma
    norm_num
    linarith [hreal', hdig'']
  nlinarith [hbound, hlogpi, hlog2, hgamma]

theorem c3Sigma_eq_neg_two_re_logDeriv_GammaR (xi : Real) :
    c3Sigma xi =
      -2 *
        (logDeriv Complex.Gammaℝ
          (((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I)).re := by
  have hs : 0 <
      ((((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I).re) := by
    simp
  have hlog :=
    Source.C1XiCenterTwoGamma.logDeriv_GammaR_eq_log_pi_add_digamma
      (s := (((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I)) hs
  have harg :
      (((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I) / 2 =
        (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2) := by
    norm_num [div_eq_mul_inv]
    ring
  rw [hlog, harg]
  unfold c3Sigma
  norm_num [Complex.div_re, Complex.mul_re, Complex.log_re]
  ring_nf

theorem c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries (xi : Real) :
    c3Sigma xi - c3Sigma 0 =
      -((∑' n : Nat,
          ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) +
                (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2))⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹))).re) := by
  let z : Complex :=
    (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)
  let z0 : Complex := ((1 / 4 : Real) : Complex)
  have hz : 0 < z.re := by
    dsimp [z]
    norm_num [Complex.div_re, Complex.mul_re]
  have hz0 : 0 < z0.re := by
    dsimp [z0]
    norm_num
  have hsix : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz
  have hs0 : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z0)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0
  have hxi :=
    Source.C1XiCenterTwoGamma.halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos hz
  have hzero :=
    Source.C1XiCenterTwoGamma.halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos hz0
  have hdiff : Complex.digamma z - Complex.digamma z0 =
      ∑' n : Nat,
        ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) + z)⁻¹) -
          (((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) + z0)⁻¹)) := by
    calc
      Complex.digamma z - Complex.digamma z0 =
          (Complex.digamma z - Complex.digamma (1 / 2 : Complex)) -
            (Complex.digamma z0 - Complex.digamma (1 / 2 : Complex)) := by
        ring
      _ = (∑' n : Nat,
          (((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) + z)⁻¹)) -
          (∑' n : Nat,
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹)) := by
        rw [hxi, hzero]
      _ = ∑' n : Nat,
          ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹)) := by
        exact (hsix.tsum_sub hs0).symm
  have hreal := congrArg Complex.re hdiff
  dsimp [c3Sigma, z, z0]
  dsimp [z, z0] at hreal
  simp only [mul_zero, zero_mul, zero_div, sub_zero]
  linarith

theorem re_c3Sigma_reciprocalDifferenceTerm (xi : Real) (n : Nat) :
    (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) +
          (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2))⁻¹) -
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹))).re =
      (xi / 2) ^ 2 /
        (((n : Real) + 1 / 4) *
          (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by
  have hn : 0 < (n : Real) + 1 / 4 := by positivity
  have hden : 0 <
      ((n : Real) + 1 / 4) *
        (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2) := by
    positivity
  simp [Complex.inv_re, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]
  field_simp
  ring

theorem re_c3Sigma_reciprocalDifferenceTerm_nonneg (xi : Real) (n : Nat) :
    0 ≤
      (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) +
            (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2))⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹))).re := by
  rw [re_c3Sigma_reciprocalDifferenceTerm]
  positivity

theorem re_c3Sigma_reciprocalDifferenceTerm_mono_of_nonneg
    {xi eta : Real} (hxi : 0 ≤ xi) (hle : xi ≤ eta) (n : Nat) :
    (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) +
          (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2))⁻¹) -
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹))).re ≤
    (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) +
          (((1 / 4 : Real) : Complex) - ((eta : Complex) * Complex.I) / 2))⁻¹) -
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹))).re := by
  rw [re_c3Sigma_reciprocalDifferenceTerm,
    re_c3Sigma_reciprocalDifferenceTerm]
  let a : Real := (n : Real) + 1 / 4
  let x : Real := xi / 2
  let y : Real := eta / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hxy : 0 ≤ x ∧ x ≤ y := by
    dsimp [x, y]
    constructor <;> linarith
  have hsq : x ^ 2 ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - x)]
  have hdx : 0 < a * (a ^ 2 + x ^ 2) := by positivity
  have hdy : 0 < a * (a ^ 2 + y ^ 2) := by positivity
  change x ^ 2 / (a * (a ^ 2 + x ^ 2)) ≤
    y ^ 2 / (a * (a ^ 2 + y ^ 2))
  apply (div_le_div_iff₀ hdx hdy).2
  calc
    x ^ 2 * (a * (a ^ 2 + y ^ 2)) =
        a ^ 3 * x ^ 2 + a * x ^ 2 * y ^ 2 := by ring
    _ ≤ a ^ 3 * y ^ 2 + a * x ^ 2 * y ^ 2 := by
      have hmul : a ^ 3 * x ^ 2 ≤ a ^ 3 * y ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ a ^ 3)
      nlinarith
    _ = y ^ 2 * (a * (a ^ 2 + x ^ 2)) := by ring

theorem c3Sigma_antitone_of_nonneg
    {xi eta : Real} (hxi : 0 ≤ xi) (hle : xi ≤ eta) :
    c3Sigma eta ≤ c3Sigma xi := by
  let zxi : Complex :=
    (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)
  let zeta : Complex :=
    (((1 / 4 : Real) : Complex) - ((eta : Complex) * Complex.I) / 2)
  let z0 : Complex := ((1 / 4 : Real) : Complex)
  have hzxi : 0 < zxi.re := by
    dsimp [zxi]
    norm_num [Complex.div_re, Complex.mul_re]
  have hzeta : 0 < zeta.re := by
    dsimp [zeta]
    norm_num [Complex.div_re, Complex.mul_re]
  have hz0 : 0 < z0.re := by
    dsimp [z0]
    norm_num
  have hsxi : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + zxi)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := by
    exact
      (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hzxi).sub
        (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0)
  have hseta : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + zeta)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := by
    exact
      (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hzeta).sub
        (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0)
  have hsum :
      (∑' n : Nat,
          (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zxi)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re) ≤
        ∑' n : Nat,
          (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zeta)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re := by
    refine (Complex.reCLM.summable hsxi).tsum_le_tsum ?_
      (Complex.reCLM.summable hseta)
    intro n
    dsimp [zxi, zeta, z0]
    simpa only [Complex.sub_re] using
      (re_c3Sigma_reciprocalDifferenceTerm_mono_of_nonneg hxi hle n)
  have hxi0 := c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries xi
  have heta0 := c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries eta
  have hxi0' :
      c3Sigma xi - c3Sigma 0 =
        -((∑' n : Nat,
          ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zxi)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re) := by
    simpa only [zxi, z0] using hxi0
  have heta0' :
      c3Sigma eta - c3Sigma 0 =
        -((∑' n : Nat,
          ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zeta)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re) := by
    simpa only [zeta, z0] using heta0
  rw [Complex.re_tsum hsxi] at hxi0'
  rw [Complex.re_tsum hseta] at heta0'
  linarith

theorem c3Sigma_le_at_zero (xi : Real) :
    c3Sigma xi ≤ c3Sigma 0 := by
  suffices hsub : c3Sigma xi - c3Sigma 0 ≤ 0 by linarith
  rw [c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries]
  let z : Complex :=
    (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)
  let z0 : Complex := ((1 / 4 : Real) : Complex)
  have hz : 0 < z.re := by
    dsimp [z]
    norm_num [Complex.div_re, Complex.mul_re]
  have hz0 : 0 < z0.re := by
    dsimp [z0]
    norm_num
  have hsix : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz
  have hs0 : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z0)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0
  have hsum : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := hsix.sub hs0
  rw [Complex.re_tsum hsum]
  have hnon : 0 ≤ ∑' n : Nat,
      (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))).re := by
    exact tsum_nonneg (fun n => by
      dsimp [z, z0]
      exact re_c3Sigma_reciprocalDifferenceTerm_nonneg xi n)
  linarith

theorem re_c3Sigma_reciprocalDifferenceTerm_pos_of_ne_zero
    {xi : Real} (hxi : xi ≠ 0) (n : Nat) :
    0 <
      (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) +
            (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2))⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹))).re := by
  rw [re_c3Sigma_reciprocalDifferenceTerm]
  have hxi' : xi / 2 ≠ 0 := div_ne_zero hxi (by norm_num)
  have hsq : 0 < (xi / 2) ^ 2 := sq_pos_of_ne_zero hxi'
  positivity

theorem c3Sigma_lt_at_zero_of_ne_zero {xi : Real} (hxi : xi ≠ 0) :
    c3Sigma xi < c3Sigma 0 := by
  suffices hsub : c3Sigma xi - c3Sigma 0 < 0 by linarith
  rw [c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries]
  let z : Complex :=
    (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)
  let z0 : Complex := ((1 / 4 : Real) : Complex)
  have hz : 0 < z.re := by
    dsimp [z]
    norm_num [Complex.div_re, Complex.mul_re]
  have hz0 : 0 < z0.re := by
    dsimp [z0]
    norm_num
  have hsix : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz
  have hs0 : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z0)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0
  have hsum : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := hsix.sub hs0
  rw [Complex.re_tsum hsum]
  have hsumreal : Summable (fun n : Nat =>
      (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))).re) :=
    Complex.reCLM.summable hsum
  have hpos := hsumreal.tsum_pos
    (fun n => by
      dsimp [z, z0]
      exact re_c3Sigma_reciprocalDifferenceTerm_nonneg xi n)
    0 (by
      dsimp [z, z0]
      exact re_c3Sigma_reciprocalDifferenceTerm_pos_of_ne_zero hxi 0)
  linarith

theorem c3Sigma_le_at_zero_sub_finite_sum (xi : Real) (N : Nat) :
    c3Sigma xi ≤ c3Sigma 0 -
      ∑ n ∈ Finset.range N,
        (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by
  suffices hsub : c3Sigma xi - c3Sigma 0 ≤
      -(∑ n ∈ Finset.range N,
        (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2))) by linarith
  rw [c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries]
  let z : Complex :=
    (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)
  let z0 : Complex := ((1 / 4 : Real) : Complex)
  have hz : 0 < z.re := by
    dsimp [z]
    norm_num [Complex.div_re, Complex.mul_re]
  have hz0 : 0 < z0.re := by
    dsimp [z0]
    norm_num
  have hsix : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz
  have hs0 : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z0)⁻¹) :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0
  have hsum : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := hsix.sub hs0
  rw [Complex.re_tsum hsum]
  have hsumreal : Summable (fun n : Nat =>
      (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))).re) :=
    Complex.reCLM.summable hsum
  have hfinite := hsumreal.sum_le_tsum (Finset.range N)
    (fun n _ => by
      dsimp [z, z0]
      exact re_c3Sigma_reciprocalDifferenceTerm_nonneg xi n)
  have hfinite' :
      (∑ n ∈ Finset.range N,
        (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2))) ≤
        ∑' n : Nat,
          (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re := by
    calc
      (∑ n ∈ Finset.range N,
          (xi / 2) ^ 2 /
            (((n : Real) + 1 / 4) *
              (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2))) =
          ∑ n ∈ Finset.range N,
            (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
                ((n : Complex) + z)⁻¹) -
              (((n : Complex) + (1 / 2 : Complex))⁻¹ -
                ((n : Complex) + z0)⁻¹))).re := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [z, z0]
        simpa only [Complex.sub_re] using
          (re_c3Sigma_reciprocalDifferenceTerm xi n).symm
      _ ≤ _ := hfinite
  linarith

theorem c3Sigma_neg_of_harmonic_certificate {K : Nat}
    (hK : (24 : Real) <
      ∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real)) :
    c3Sigma (2 * ((K : Real) + 1)) < 0 := by
  have hterm : ∀ n ∈ Finset.range K,
      (1 / 2 : Real) * (1 / ((n : Real) + 1)) ≤
        (((2 * ((K : Real) + 1)) / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 +
              ((2 * ((K : Real) + 1)) / 2) ^ 2))) := by
    intro n hn
    have hnK : n < K := Finset.mem_range.mp hn
    let a : Real := (n : Real) + 1 / 4
    let b : Real := (n : Real) + 1
    let x : Real := (2 * ((K : Real) + 1)) / 2
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have hxab : a ≤ b := by dsimp [a, b]; norm_num
    have hnb : b ≤ x := by
      dsimp [b, x]
      have hcast : (n : Real) + 1 ≤ (K : Real) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hnK)
      linarith
    have hax : a ≤ x := hxab.trans hnb
    have hsq : a ^ 2 ≤ x ^ 2 := by
      nlinarith [sq_nonneg (x - a)]
    have hden₁ : 0 < 2 * b := by positivity
    have hden₂ : 0 < a * (a ^ 2 + x ^ 2) := by positivity
    have hrewrite : (1 / 2 : Real) * (1 / b) = 1 / (2 * b) := by
      field_simp
    rw [hrewrite]
    change 1 / (2 * b) ≤ x ^ 2 / (a * (a ^ 2 + x ^ 2))
    apply (div_le_div_iff₀ hden₁ hden₂).2
    calc
      1 * (a * (a ^ 2 + x ^ 2)) ≤
          1 * (b * (a ^ 2 + x ^ 2)) := by gcongr
      _ ≤ 1 * (b * (2 * x ^ 2)) := by
        gcongr
        nlinarith
      _ = x ^ 2 * (2 * b) := by ring
  have hsum :
      (∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1))) ≤
        ∑ n ∈ Finset.range K,
          (((2 * ((K : Real) + 1)) / 2) ^ 2 /
            (((n : Real) + 1 / 4) *
              (((n : Real) + 1 / 4) ^ 2 +
                ((2 * ((K : Real) + 1)) / 2) ^ 2))) := by
    exact Finset.sum_le_sum (fun n hn => hterm n hn)
  have hhalf : (12 : Real) <
      ∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1)) := by
    have heq :
        (∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1))) =
          (1 / 2 : Real) *
            (∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real)) := by
      rw [Finset.mul_sum]
    rw [heq]
    nlinarith [hK]
  have hfinite := c3Sigma_le_at_zero_sub_finite_sum
    (2 * ((K : Real) + 1)) K
  have hsum' : (12 : Real) <
      ∑ n ∈ Finset.range K,
        (((2 * ((K : Real) + 1)) / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 +
              ((2 * ((K : Real) + 1)) / 2) ^ 2))) :=
    lt_of_lt_of_le hhalf hsum
  calc
    c3Sigma (2 * ((K : Real) + 1)) ≤
        c3Sigma 0 -
          ∑ n ∈ Finset.range K,
            (((2 * ((K : Real) + 1)) / 2) ^ 2 /
              (((n : Real) + 1 / 4) *
                (((n : Real) + 1 / 4) ^ 2 +
                  ((2 * ((K : Real) + 1)) / 2) ^ 2))) := hfinite
    _ < 0 := by linarith [c3Sigma_zero_lt_twelve, hsum']

theorem c3Sigma_neg_at_exp_ceiling :
    c3Sigma (2 * ((Nat.ceil (Real.exp 25) : Nat) + 1)) < 0 := by
  let K : Nat := Nat.ceil (Real.exp 25)
  have hceil : Real.exp 25 ≤ (K : Real) := by
    dsimp [K]
    exact Nat.le_ceil _
  have hKpos : 0 < (K : Real) := by
    have hexp : 0 < Real.exp 25 := Real.exp_pos _
    linarith
  have hlogK : 25 ≤ Real.log (K : Real) := by
    have hlog := Real.log_le_log (Real.exp_pos 25) hceil
    simpa using hlog
  have hlogK1 : (24 : Real) < Real.log ((K : Real) + 1) := by
    have hloglt : Real.log (K : Real) < Real.log ((K : Real) + 1) :=
      Real.log_lt_log hKpos (by linarith)
    linarith
  have hharmonic : (24 : Real) <
      ∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real) := by
    have hlog := log_add_one_le_harmonic K
    have hlog' : Real.log ((K : Real) + 1) ≤ (harmonic K : Real) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hlog
    have hsum_eq : (harmonic K : Real) =
        ∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real) := by
      simp [harmonic]
    exact lt_of_lt_of_le hlogK1 (hsum_eq ▸ hlog')
  have hneg := c3Sigma_neg_of_harmonic_certificate hharmonic
  simpa [K] using hneg

theorem exists_c3Sigma_neg : ∃ xi : Real, c3Sigma xi < 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (c3Sigma 0)
  have hdiv :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (Filter.eventually_gt_atTop (2 * (N : Real)))
  obtain ⟨K, hK⟩ := hdiv.exists
  let xi : Real := 2 * (K + 1)
  have hterm : ∀ n ∈ Finset.range K,
      (1 / 2 : Real) * (1 / ((n : Real) + 1)) ≤
        (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by
    intro n hn
    have hnK : n < K := Finset.mem_range.mp hn
    let a : Real := (n : Real) + 1 / 4
    let b : Real := (n : Real) + 1
    let x : Real := xi / 2
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hb : 0 < b := by
      dsimp [b]
      positivity
    have hxab : a ≤ b := by
      dsimp [a, b]
      norm_num
    have hnb : b ≤ x := by
      dsimp [b, x, xi]
      have hcast : (n : Real) + 1 ≤ (K : Real) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hnK)
      linarith
    have hax : a ≤ x := hxab.trans hnb
    have hsq : a ^ 2 ≤ x ^ 2 := by
      nlinarith [sq_nonneg (x - a)]
    have hden₁ : 0 < 2 * b := by positivity
    have hden₂ : 0 < a * (a ^ 2 + x ^ 2) := by positivity
    have hrewrite : (1 / 2 : Real) * (1 / b) = 1 / (2 * b) := by
      field_simp
    rw [hrewrite]
    change 1 / (2 * b) ≤ x ^ 2 / (a * (a ^ 2 + x ^ 2))
    apply (div_le_div_iff₀ hden₁ hden₂).2
    calc
      1 * (a * (a ^ 2 + x ^ 2)) ≤
          1 * (b * (a ^ 2 + x ^ 2)) := by
        gcongr
      _ ≤ 1 * (b * (2 * x ^ 2)) := by
        gcongr
        nlinarith
      _ = x ^ 2 * (2 * b) := by ring
  have hsum :
      (∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1))) ≤
        ∑ n ∈ Finset.range K,
          (xi / 2) ^ 2 /
            (((n : Real) + 1 / 4) *
              (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by
    exact Finset.sum_le_sum (fun n hn => hterm n hn)
  have hhalf : (N : Real) <
      ∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1)) := by
    have hK' : 2 * (N : Real) <
        ∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real) := by
      simpa using hK
    have heq :
        (∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1))) =
            (1 / 2 : Real) *
            (∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real)) := by
      rw [Finset.mul_sum]
    rw [heq]
    nlinarith [hK']
  have hfinite := c3Sigma_le_at_zero_sub_finite_sum xi K
  dsimp [xi] at hfinite hterm hsum
  have hsum' : (N : Real) <
      ∑ n ∈ Finset.range K,
        ((2 * (K + 1) / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (2 * (K + 1) / 2) ^ 2))) := by
    exact lt_of_lt_of_le hhalf hsum
  refine ⟨2 * (K + 1), ?_⟩
  calc
    c3Sigma (2 * (K + 1)) ≤
        c3Sigma 0 -
          ∑ n ∈ Finset.range K,
            ((2 * (K + 1) / 2) ^ 2 /
              (((n : Real) + 1 / 4) *
                (((n : Real) + 1 / 4) ^ 2 + (2 * (K + 1) / 2) ^ 2))) := hfinite
    _ < 0 := by linarith [hN, hsum']

theorem c3Sigma_neg_eq (xi : Real) :
    c3Sigma (-xi) = c3Sigma xi := by
  let zpos : Complex :=
    (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)
  let zneg : Complex :=
    (((1 / 4 : Real) : Complex) - ((-xi : Complex) * Complex.I) / 2)
  let z0 : Complex := ((1 / 4 : Real) : Complex)
  have hzpos : 0 < zpos.re := by
    dsimp [zpos]
    norm_num [Complex.div_re, Complex.mul_re]
  have hzneg : 0 < zneg.re := by
    dsimp [zneg]
    norm_num [Complex.div_re, Complex.mul_re]
  have hz0 : 0 < z0.re := by
    dsimp [z0]
    norm_num
  have hsp : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + zpos)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := by
    exact
      (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hzpos).sub
        (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0)
  have hsn : Summable (fun n : Nat =>
      ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + zneg)⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + z0)⁻¹))) := by
    exact
      (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hzneg).sub
        (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0)
  have hreal :
      (∑' n : Nat,
          (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zneg)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re) =
        ∑' n : Nat,
          (((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zpos)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re := by
    apply tsum_congr
    intro n
    dsimp [zneg, zpos, z0]
    calc
      _ = ((-xi) / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + ((-xi) / 2) ^ 2)) := by
        simpa only [Complex.sub_re, Complex.ofReal_neg] using
          (re_c3Sigma_reciprocalDifferenceTerm (-xi) n)
      _ = (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by ring
      _ = _ := by
        simpa only [Complex.sub_re] using
          (re_c3Sigma_reciprocalDifferenceTerm xi n).symm
  have hneg := c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries (-xi)
  have hpos := c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries xi
  have hneg' :
      c3Sigma (-xi) - c3Sigma 0 =
        -((∑' n : Nat,
          ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zneg)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re) := by
    simpa only [zneg, z0, Complex.ofReal_neg] using hneg
  have hpos' :
      c3Sigma xi - c3Sigma 0 =
        -((∑' n : Nat,
          ((((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + zpos)⁻¹) -
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + z0)⁻¹))).re) := by
    simpa only [zpos, z0] using hpos
  rw [Complex.re_tsum hsn] at hneg'
  rw [Complex.re_tsum hsp] at hpos'
  rw [hreal] at hneg'
  linarith

theorem exists_c3Sigma_negative_tail :
    ∃ T : Real, 0 ≤ T ∧ ∀ xi : Real, T ≤ xi → c3Sigma xi < 0 := by
  obtain ⟨t, ht⟩ := exists_c3Sigma_neg
  refine ⟨|t|, abs_nonneg t, ?_⟩
  have hT : c3Sigma |t| < 0 := by
    by_cases hnonneg : 0 ≤ t
    · simpa [abs_of_nonneg hnonneg] using ht
    · have hneg : t < 0 := lt_of_not_ge hnonneg
      rw [abs_of_neg hneg]
      rw [c3Sigma_neg_eq t]
      exact ht
  intro xi hxi
  exact lt_of_le_of_lt
    (c3Sigma_antitone_of_nonneg (abs_nonneg t) hxi) hT

end Dev
end ConnesWeilRH
