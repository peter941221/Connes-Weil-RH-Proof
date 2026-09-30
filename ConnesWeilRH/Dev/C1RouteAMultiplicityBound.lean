import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ConnesWeilRH.Source.C1RouteAMultiplicityBound

open CC20ZetaCounting C1SpectralSummability C1RouteAItem5Arithmetic

theorem completedRiemannXi_two_eq : completedRiemannXi 2 = (Real.pi : Complex) / 3 := by
  have hpi : (Real.pi : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hgamma : Complex.Gammaℝ 2 = (Real.pi : Complex)⁻¹ := by
    rw [Complex.Gammaℝ_def]
    norm_num [Complex.cpow_neg_one, Complex.Gamma_one]
  have hzeta := riemannZeta_def_of_ne_zero (s := (2 : Complex)) (by norm_num)
  rw [riemannZeta_two, hgamma] at hzeta
  have hcompleted : completedRiemannZeta 2 = (Real.pi : Complex) / 6 := by
    field_simp [hpi] at hzeta ⊢
    linear_combination -hzeta
  rw [completedRiemannXi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    hcompleted]
  ring

theorem norm_completedRiemannXi_two_eq : ‖completedRiemannXi 2‖ = Real.pi / 3 := by
  rw [completedRiemannXi_two_eq, norm_div]
  simp [Complex.norm_real, abs_of_pos Real.pi_pos]

theorem gamma_quarter_le : Real.Gamma (1 / 4) ≤ 37 / 10 := by
  have hpi : Real.pi ≤ (71 / 40 : Real) ^ 2 := by
    linarith [Real.pi_lt_d4]
  have hsqrt : Real.sqrt Real.pi ≤ 71 / 40 :=
    (Real.sqrt_le_left (by norm_num)).mpr hpi
  have hhalf : Real.Gamma (5 / 2) = (3 / 4 : Real) * Real.sqrt Real.pi := by
    have hrec1 := Real.Gamma_add_one (s := (1 / 2 : Real)) (by norm_num)
    have hrec2 := Real.Gamma_add_one (s := (3 / 2 : Real)) (by norm_num)
    rw [Real.Gamma_one_half_eq] at hrec1
    norm_num at hrec1 hrec2
    nlinarith
  have hupper : Real.Gamma (5 / 2) ≤ 213 / 160 := by
    rw [hhalf]
    linarith
  have hmid := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := (2 : Real)) (t := (5 / 2 : Real))
    (a := (1 / 2 : Real)) (b := (1 / 2 : Real))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.Gamma_two] at hmid
  rw [← Real.sqrt_eq_rpow] at hmid
  have hroot : Real.sqrt (Real.Gamma (5 / 2)) ≤ 37 / 32 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    linarith
  have hrec1 := Real.Gamma_add_one (s := (1 / 4 : Real)) (by norm_num)
  have hrec2 := Real.Gamma_add_one (s := (5 / 4 : Real)) (by norm_num)
  norm_num at hrec1 hrec2
  linarith

theorem pi_inv_quarter_le : (1 / Real.pi) ^ (1 / 4 : Real) ≤ 19 / 25 := by
  have hbase : (1 / Real.pi) ≤ (19 / 25 : Real) ^ 4 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hpow : ((1 / Real.pi) ^ (1 / 4 : Real)) ^ (4 : Nat) = 1 / Real.pi := by
    simpa using Real.rpow_inv_natCast_pow (x := 1 / Real.pi) (n := 4)
      (by positivity) (by norm_num)
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by positivity) _) (by norm_num)
    (by norm_num : (4 : Nat) ≠ 0)).mp
  rw [hpow]
  exact hbase

theorem kernelSmallMomentConstant_le : kernelSmallMomentConstant ≤ 703 / 250 := by
  unfold kernelSmallMomentConstant
  have hproduct := mul_le_mul pi_inv_quarter_le gamma_quarter_le
    (Real.Gamma_pos_of_pos (by norm_num : (0 : Real) < 1 / 4)).le
    (by norm_num : (0 : Real) ≤ 19 / 25)
  norm_num at hproduct ⊢
  exact hproduct

theorem kernelTailConstant_le : completedRiemannXiKernelTailConstant ≤ 19 / 9 := by
  have hexp : (19 : Real) ≤ Real.exp Real.pi := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (3 : Real)) (by norm_num) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    have hmono := Real.exp_le_exp.mpr Real.pi_gt_three.le
    linarith
  have hinv : Real.exp (-Real.pi) ≤ 1 / 19 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : Real) < 19) hexp
  unfold completedRiemannXiKernelTailConstant
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-Real.pi))).mpr
  linarith

theorem xi_two_log_abs_le : |Real.log ‖completedRiemannXi 2‖| ≤ 1 / 20 := by
  rw [norm_completedRiemannXi_two_eq]
  have hunit : (1 : Real) ≤ Real.pi / 3 := by linarith [Real.pi_gt_three]
  rw [abs_of_nonneg (Real.log_nonneg hunit)]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : Real) < Real.pi / 3)
  linarith [Real.pi_lt_d2]

theorem spectralMultiplicityConstant_le_coarse : spectralMultiplicityConstant ≤ 128.65 := by
  have hfixed : xiGrowthFixedConstant ≤ 2 * (19 / 9) * (703 / 250 + 1) := by
    unfold xiGrowthFixedConstant
    have hsmall : kernelSmallMomentConstant + 1 ≤ 703 / 250 + 1 := by
      linarith [kernelSmallMomentConstant_le]
    have htail := mul_le_mul_of_nonneg_left kernelTailConstant_le (by norm_num : (0 : Real) ≤ 2)
    exact mul_le_mul htail hsmall
      (add_nonneg kernelSmallMomentConstant_nonneg zero_le_one) (by norm_num)
  unfold spectralMultiplicityConstant
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : Real) < 2))).mpr
  have hlog : (693 / 1000 : Real) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hxi := xi_two_log_abs_le
  nlinarith

theorem spectralMultiplicityConstant_lt_originalProxy2248 :
    spectralMultiplicityConstant < (128.70692502980964 : Real) := by
  exact lt_of_le_of_lt spectralMultiplicityConstant_le_coarse (by norm_num)

theorem spectralMultiplicityConstant_le_multProxy2248 :
    spectralMultiplicityConstant ≤ multProxy2248 := by
  exact spectralMultiplicityConstant_le_coarse.trans (by norm_num [multProxy2248])

end ConnesWeilRH.Source.C1RouteAMultiplicityBound
