import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderStructure

/-! Reflection transports the certified half-interval integrals to the actual
smoothSeed derivative masses. No derivative-budget hypotheses occur here. -/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

theorem norm_iteratedDeriv_one_sub3102 (n : Nat) (hn : 0 < n) (x : Real) :
    ‖iteratedDeriv n Real.smoothTransition (1 - x)‖ =
      ‖iteratedDeriv n Real.smoothTransition x‖ := by
  have heq : (fun y : Real => Real.smoothTransition (1 - y)) =
      (fun y : Real => 1 - Real.smoothTransition y) :=
    funext smoothTransition_one_sub
  have h := congrFun (congrArg (iteratedDeriv n) heq) x
  rw [iteratedDeriv_comp_const_sub, iteratedDeriv_const_sub hn,
    iteratedDeriv_neg] at h
  have habs := congrArg norm h
  simpa only [Pi.smul_apply, norm_smul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul] using habs

theorem derivOrderL1_smoothSeed_eq_half_integral3102 (n : Nat) (hn : 0 < n) :
    derivOrderL1 n smoothSeed =
      4 * (∫ x in (0 : Real)..(1 / 2), ‖iteratedDeriv n Real.smoothTransition x‖) := by
  have hc : Continuous (fun x : Real => ‖iteratedDeriv n Real.smoothTransition x‖) :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous
  have hreflect : (∫ x in (1 / 2 : Real)..1,
      ‖iteratedDeriv n Real.smoothTransition x‖) =
      ∫ x in (0 : Real)..(1 / 2), ‖iteratedDeriv n Real.smoothTransition x‖ := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (f := fun x : Real => ‖iteratedDeriv n Real.smoothTransition x‖)
      (a := (0 : Real)) (b := 1 / 2) (1 : Real)
    rw [show (1 : Real) - 1 / 2 = 1 / 2 by norm_num, sub_zero] at hcomp
    rw [← hcomp]
    exact intervalIntegral.integral_congr (fun x _ => norm_iteratedDeriv_one_sub3102 n hn x)
  have hoff (x : Real) (hx : x ∉ Set.Icc (0 : Real) 1) :
      ‖iteratedDeriv n Real.smoothTransition x‖ = 0 := by
    have hz : iteratedDeriv n Real.smoothTransition x = 0 := by
      by_contra hne
      exact hx (support_iteratedDeriv_smoothTransition_subset n hn
        (Function.mem_support.mpr hne))
    rw [hz, norm_zero]
  have hfull : (∫ x : Real, ‖iteratedDeriv n Real.smoothTransition x‖) =
      ∫ x in (0 : Real)..1, ‖iteratedDeriv n Real.smoothTransition x‖ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num)]
  rw [derivOrderL1_smoothSeed_eq n hn, hfull,
    ← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), hreflect]
  ring

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
