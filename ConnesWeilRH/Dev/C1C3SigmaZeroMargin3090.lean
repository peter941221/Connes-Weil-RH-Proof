import ConnesWeilRH.Dev.C1C3SigmaKernel
import ConnesWeilRH.Dev.C1XiCenterTwoGamma

/-!
# Route A c3Sigma zero margin reduction (record 3090)

The exact remaining special-function obligation is a strict upper bound on the
real part of `digamma (1/4)`. This module records the reduction without hiding
that bound behind a numerical constant.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3SigmaZeroMargin3090

open ConnesWeilRH.Source.C1XiCenterTwoGamma

noncomputable section

def quarterDigammaGapTerm (n : Nat) : Real :=
  1 / ((n : Real) + 1 / 4) - 1 / ((n : Real) + 1 / 2)

theorem quarterDigammaGapTerm_nonneg (n : Nat) :
    0 ≤ quarterDigammaGapTerm n := by
  unfold quarterDigammaGapTerm
  have hn : 0 < (n : Real) + 1 / 4 := by positivity
  have hn' : 0 < (n : Real) + 1 / 2 := by positivity
  apply sub_nonneg.mpr
  apply one_div_le_one_div_of_le
  · exact hn
  · linarith

theorem quarterDigammaGapTerm_zero_pos :
    0 < quarterDigammaGapTerm 0 := by
  unfold quarterDigammaGapTerm
  norm_num

theorem digamma_quarter_lt_half_of_reciprocal_series :
    (Complex.digamma ((1 / 4 : Real) : Complex)).re <
      (Complex.digamma (1 / 2 : Complex)).re := by
  let a : Nat → Real := quarterDigammaGapTerm
  let f : Nat → Complex := fun n : Nat =>
    ((n : Complex) + (1 / 2 : Complex))⁻¹ -
      ((n : Complex) + (((1 / 4 : Real) : Complex)))⁻¹
  have hcomplex : Summable f := by
    dsimp [f]
    exact summable_halfAnchorGaussReciprocalSeries (by norm_num)
  have hreal_neg : Summable (fun n : Nat => -a n) := by
    convert Complex.reCLM.summable hcomplex using 1
    funext n
    dsimp [f]
    simp [a, quarterDigammaGapTerm, Complex.inv_re, Complex.normSq_apply]
  have hreal : Summable a := by
    simpa [a] using hreal_neg.neg
  have hsum_pos : 0 < ∑' n : Nat, a n := by
    change 0 < ∑' n : Nat, quarterDigammaGapTerm n
    simpa using (hreal.tsum_lt_tsum_of_nonneg
      (f := fun _ : Nat => (0 : Real))
      (fun _ => le_rfl)
      (fun n => quarterDigammaGapTerm_nonneg n)
      quarterDigammaGapTerm_zero_pos)
  have hseries := halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos
    (z := ((1 / 4 : Real) : Complex)) (by norm_num)
  have hseries_f : (∑' n : Nat, f n) =
      Complex.digamma ((1 / 4 : Real) : Complex) -
        Complex.digamma (1 / 2 : Complex) := by
    simpa [f] using hseries
  have hre := congrArg Complex.re hseries_f
  have hterm : ∀ n : Nat,
      Complex.re (f n) = -a n := by
    intro n
    dsimp [f]
    simp [a, quarterDigammaGapTerm, Complex.inv_re, Complex.normSq_apply]
  have hre' : (∑' n : Nat, -a n) =
      Complex.re (∑' n : Nat, f n) := by
    rw [Complex.re_tsum hcomplex]
    simp_rw [hterm]
  have hneg : (∑' n : Nat, -a n) < 0 := by
    calc
      (∑' n : Nat, -a n) = -∑' n : Nat, a n := tsum_neg
      _ < 0 := neg_lt_zero.mpr hsum_pos
  have hdiff : (∑' n : Nat, -a n) =
      (Complex.digamma ((1 / 4 : Real) : Complex) -
        Complex.digamma (1 / 2 : Complex)).re := hre'.trans hre
  have hineq :
      (Complex.digamma ((1 / 4 : Real) : Complex) -
        Complex.digamma (1 / 2 : Complex)).re < 0 := by
    linarith [hneg, hdiff]
  have hineq' :
      (Complex.digamma ((1 / 4 : Real) : Complex)).re -
        (Complex.digamma (1 / 2 : Complex)).re < 0 := by
    simpa only [Complex.sub_re] using hineq
  linarith

theorem digamma_half_re_lt_log_pi :
    (Complex.digamma ((1 / 2 : Real) : Complex)).re < Real.log Real.pi := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgamma : 0 ≤ Real.eulerMascheroniConstant :=
    (lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant).le
  have hlogpi : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have hlog2_re : (Complex.log (2 : Complex)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  have hhalf_eq :
      (Complex.digamma ((1 / 2 : Real) : Complex)).re =
        -2 * Real.log 2 - Real.eulerMascheroniConstant := by
    rw [show ((1 / 2 : Real) : Complex) = (1 / 2 : Complex) by norm_num,
      Complex.digamma_one_half]
    norm_num [Complex.sub_re, Complex.neg_re, Complex.mul_re]
    rw [hlog2_re]
  calc
    (Complex.digamma ((1 / 2 : Real) : Complex)).re =
        -2 * Real.log 2 - Real.eulerMascheroniConstant := hhalf_eq
    _ < Real.log Real.pi := by nlinarith

end

theorem c3Sigma_zero_pos_of_digamma_re_lt_log_pi
    (hdig : (Complex.digamma ((1 / 4 : Real) : Complex)).re < Real.log Real.pi) :
    0 < c3Sigma 0 := by
  simpa [c3Sigma] using (sub_pos.mpr hdig)

theorem c3Sigma_zero_pos : 0 < c3Sigma 0 := by
  apply c3Sigma_zero_pos_of_digamma_re_lt_log_pi
  exact (digamma_quarter_lt_half_of_reciprocal_series.trans
    (by simpa only [show ((1 / 2 : Real) : Complex) = (1 / 2 : Complex) by norm_num]
      using digamma_half_re_lt_log_pi))

theorem digamma_zero_margin_target :
    0 < c3Sigma 0 ↔
      (Complex.digamma ((1 / 4 : Real) : Complex)).re < Real.log Real.pi := by
  simp [c3Sigma]

end C1C3SigmaZeroMargin3090
end Dev
end ConnesWeilRH
