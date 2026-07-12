/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogHaar
import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Logarithmic transport of the finite-window Haar integral

This module proves the actual change of variables from the parameterized
subtype measure `d rho / rho` to Lebesgue measure in the coordinate
`rho = exp t`.  The equality is stated for one ambient continuous function,
so both sides refer to the same test rather than unrelated witnesses.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped Interval

theorem integral_cc20WindowHaarMeasure_eq_logInterval_of_continuousOn
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc (1 / lambda) lambda)) :
    (∫ rho, f rho.1 ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda, f (Real.exp t) := by
  rw [integral_cc20WindowHaarMeasure_eq_smul]
  change
    (∫ rho : {x : ℝ // x ∈ Set.Icc (1 / lambda) lambda},
      (1 / rho.1) • f rho.1
        ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc
    (fun rho : ℝ => (1 / rho) • f rho)]
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hleft : Real.exp (-Real.log lambda) = 1 / lambda := by
    rw [Real.exp_neg, Real.exp_log hlambda_pos]
    exact inv_eq_one_div lambda
  have hright : Real.exp (Real.log lambda) = lambda :=
    Real.exp_log hlambda_pos
  have hlog_pos : 0 < Real.log lambda := Real.log_pos hlambda
  have hlog_order : -Real.log lambda ≤ Real.log lambda := by linarith
  have himage :
      Real.exp '' [[-Real.log lambda, Real.log lambda]] ⊆
        Set.Icc (1 / lambda) lambda := by
    intro rho hrho
    rcases hrho with ⟨t, ht, rfl⟩
    have ht' : t ∈ Set.Icc (-Real.log lambda) (Real.log lambda) := by
      simpa [Set.uIcc_of_le hlog_order] using ht
    constructor
    · rw [← hleft]
      exact Real.exp_le_exp.mpr ht'.1
    · rw [← hright]
      exact Real.exp_le_exp.mpr ht'.2
  let g : ℝ → ℂ := fun rho => (1 / rho) • f rho
  have hg : ContinuousOn g
      (Real.exp '' [[-Real.log lambda, Real.log lambda]]) := by
    intro rho hrho
    rcases hrho with ⟨t, ht, rfl⟩
    exact
      (continuousAt_const.div continuousAt_id
        (Real.exp_ne_zero t)).continuousWithinAt.smul
          ((hf _ (himage ⟨t, ht, rfl⟩)).mono himage)
  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (a := -Real.log lambda) (b := Real.log lambda)
    (f := Real.exp) (f' := Real.exp) (g := g)
    (fun t _ht => Real.hasDerivAt_exp t)
    Real.continuous_exp.continuousOn hg
  rw [hleft, hright] at hsub
  have hwindow_le : 1 / lambda ≤ lambda :=
    (div_le_iff₀ hlambda_pos).2 (by nlinarith)
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hwindow_le]
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp [g]

theorem integral_cc20WindowHaarMeasure_eq_logInterval
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ rho, f rho.1 ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda, f (Real.exp t) :=
  integral_cc20WindowHaarMeasure_eq_logInterval_of_continuousOn
    lambda hlambda f hf.continuousOn

theorem integral_cc20WindowHaarMeasure_eq_logInterval_real
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ rho, f rho.1 ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda, f (Real.exp t) := by
  have h := integral_cc20WindowHaarMeasure_eq_logInterval
    lambda hlambda (fun rho => (f rho : ℂ))
      (Complex.continuous_ofReal.comp hf)
  change
    (∫ rho, (f rho.1 : ℂ) ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda, (f (Real.exp t) : ℂ) at h
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  exact Complex.ofReal_injective h

theorem integral_cc20WindowHaarMeasure_eq_logInterval_real_of_continuousOn
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (1 / lambda) lambda)) :
    (∫ rho, f rho.1 ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda, f (Real.exp t) := by
  have h := integral_cc20WindowHaarMeasure_eq_logInterval_of_continuousOn
    lambda hlambda (fun rho => (f rho : ℂ))
      (Complex.continuous_ofReal.comp_continuousOn hf)
  change
    (∫ rho, (f rho.1 : ℂ) ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda, (f (Real.exp t) : ℂ) at h
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  exact Complex.ofReal_injective h

end CC20Concrete
end Source
end ConnesWeilRH
