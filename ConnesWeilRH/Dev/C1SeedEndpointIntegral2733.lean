import ConnesWeilRH.Dev.C1SeedEndpointMajorants2732
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Endpoint integral certificates for the exact transition derivative owner. -/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory

noncomputable section

set_option exponentiation.threshold 5000

def seedEndpointCharge2733 (n : ℕ) : ℝ :=
  32 * (endpointTransitionCoef2732 n : ℝ) * (1 / 4096 : ℝ) *
    (4096 : ℝ) ^ (2 * n) / (2 : ℝ) ^ 4096

theorem hasDerivAt_pow_mul_exp_neg2733 (m : ℕ) (hm : 0 < m) (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ m * Real.exp (-y))
      (t ^ (m - 1) * Real.exp (-t) * ((m : ℝ) - t)) t := by
  have hp : t ^ (m - 1) * t = t ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ m by omega)]
  have hd := ((hasDerivAt_id t).pow m).mul ((hasDerivAt_id t).neg.exp)
  apply hd.congr_deriv
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
  rw [← hp]
  ring

theorem antitoneOn_pow_mul_exp_neg2733 (m : ℕ) (hm : 0 < m) :
    AntitoneOn (fun t : ℝ => t ^ m * Real.exp (-t)) (Set.Ici (m : ℝ)) := by
  have hc : Continuous (fun t : ℝ => t ^ m * Real.exp (-t)) := by fun_prop
  have hd : Differentiable ℝ (fun t : ℝ => t ^ m * Real.exp (-t)) := by fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ici (m : ℝ)) hc.continuousOn hd.differentiableOn
  intro t ht
  rw [interior_Ici, Set.mem_Ioi] at ht
  have ht0 : 0 ≤ t := (Nat.cast_nonneg m).trans ht.le
  rw [(hasDerivAt_pow_mul_exp_neg2733 m hm t).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (pow_nonneg ht0 _) (Real.exp_nonneg _)) (by linarith)

theorem inverse_power_exp_uniform2733 (m : ℕ) (hm : 0 < m) (hmcap : m ≤ 4096)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4096) :
    (x⁻¹) ^ m * Real.exp (-x⁻¹) ≤ (4096 : ℝ) ^ m * Real.exp (-4096) := by
  have hmx : (m : ℝ) ≤ 4096 := by exact_mod_cast hmcap
  have hu : (4096 : ℝ) ≤ x⁻¹ := by
    have h := one_div_le_one_div_of_le hx0 hx
    norm_num [one_div] at h
    exact h
  exact antitoneOn_pow_mul_exp_neg2733 m hm hmx (hmx.trans hu) hu

theorem exp_neg_4096_le_inv_pow2733 :
    Real.exp (-4096 : ℝ) ≤ ((2 : ℝ) ^ 4096)⁻¹ := by
  have he : Real.exp (4096 : ℝ) = (Real.exp 1) ^ 4096 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul (1 : ℝ) 4096
  have hp : (2 : ℝ) ^ 4096 ≤ (Real.exp 1) ^ 4096 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 4096
  rw [Real.exp_neg, he]
  simpa only [one_div] using
    one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) 4096) hp

theorem norm_iteratedDeriv_transition_uniform2733 (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 7)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4096) :
    ‖iteratedDeriv n Real.smoothTransition x‖ ≤
      8 * (endpointTransitionCoef2732 n : ℝ) * (4096 : ℝ) ^ (2 * n) /
        (2 : ℝ) ^ 4096 := by
  have hpoint := abs_iteratedDeriv_smoothTransition_endpoint2732 n hn hx0
    (show x ≤ 1 / 2 by linarith)
  have hmax := inverse_power_exp_uniform2733 (2 * n) (by omega) (by omega) hx0 hx
  rw [Real.norm_eq_abs]
  apply hpoint.trans
  calc
    8 * (endpointTransitionCoef2732 n : ℝ) * (x⁻¹) ^ (2 * n) * Real.exp (-x⁻¹) =
        (8 * (endpointTransitionCoef2732 n : ℝ)) *
          ((x⁻¹) ^ (2 * n) * Real.exp (-x⁻¹)) := by ring
    _ ≤ (8 * (endpointTransitionCoef2732 n : ℝ)) *
          ((4096 : ℝ) ^ (2 * n) * Real.exp (-4096)) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ ≤ (8 * (endpointTransitionCoef2732 n : ℝ)) *
          ((4096 : ℝ) ^ (2 * n) * ((2 : ℝ) ^ 4096)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left exp_neg_4096_le_inv_pow2733 (by positivity))
        (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem transition_endpoint_integral_le_charge2733 (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 7) :
    4 * (∫ x in (0 : ℝ)..(1 / 4096), ‖iteratedDeriv n Real.smoothTransition x‖) ≤
      seedEndpointCharge2733 n := by
  let B : ℝ := 8 * (endpointTransitionCoef2732 n : ℝ) *
    (4096 : ℝ) ^ (2 * n) / (2 : ℝ) ^ 4096
  have hc : Continuous (fun x : ℝ => ‖iteratedDeriv n Real.smoothTransition x‖) :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (show (0 : ℝ) ≤ 1 / 4096 by norm_num)
    (hc.intervalIntegrable 0 (1 / 4096))
    (continuous_const.intervalIntegrable (0 : ℝ) (1 / 4096))
    (fun x hx => norm_iteratedDeriv_transition_uniform2733 n hn0 hn hx.1 hx.2.le)
  change (∫ x in (0 : ℝ)..(1 / 4096), ‖iteratedDeriv n Real.smoothTransition x‖) ≤
    ∫ _ in (0 : ℝ)..(1 / 4096), B at hi
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  calc
    4 * (∫ x in (0 : ℝ)..(1 / 4096), ‖iteratedDeriv n Real.smoothTransition x‖) ≤
        4 * ((1 / 4096 : ℝ) * B) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = seedEndpointCharge2733 n := by unfold B seedEndpointCharge2733; ring

theorem seedEndpointCharge_four_lt2733 :
    seedEndpointCharge2733 4 < (1 : ℝ) / (10 : ℝ) ^ 1000 := by
  norm_num [seedEndpointCharge2733, endpointTransitionCoef2732]

theorem seedEndpointCharge_seven_lt2733 :
    seedEndpointCharge2733 7 < (1 : ℝ) / (10 : ℝ) ^ 1000 := by
  norm_num [seedEndpointCharge2733, endpointTransitionCoef2732]

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
