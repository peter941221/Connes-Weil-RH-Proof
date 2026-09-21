/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3GammaRBound

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

end Dev
end ConnesWeilRH
