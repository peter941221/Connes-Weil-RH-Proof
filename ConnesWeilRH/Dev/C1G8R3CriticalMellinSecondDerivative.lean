/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24ArchimedeanCarrier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact second chain rule for the critical Mellin profile

The carrier source already proves the first derivative of the critical Mellin
profile.  This leaf records its exact second chain rule and an absolute
integrability bound for the resulting concrete profile on the Schwartz core.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open MeasureTheory Set Filter
open scoped FourierTransform

noncomputable def ccm24CriticalMellinLogProfileSecondDerivFormula
    (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  (2 * (Real.exp (-t / 2) * Real.exp (-t)) : ℝ) •
      (SchwartzMap.derivCLM ℝ ℂ f) (Real.exp (-t)) +
    (Real.exp (-t / 2) * Real.exp (-t) ^ 2 : ℝ) •
      (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ f))
        (Real.exp (-t)) +
    ((1 / 4 : ℝ) * Real.exp (-t / 2)) • f (Real.exp (-t))

noncomputable def ccm24CriticalMellinLogProfileFirstDerivFormula
    (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  ccm24CriticalMellinLogProfileChainDeriv f t +
    ((-1 / 2 : ℝ) * Real.exp (-t / 2)) • f (Real.exp (-t))

theorem hasDerivAt_ccm24CriticalMellinLogProfileFirstDeriv_formula
    (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        ccm24CriticalMellinLogProfileChainDeriv f u +
          ((-1 / 2 : ℝ) * Real.exp (-u / 2)) • f (Real.exp (-u)))
      (ccm24CriticalMellinLogProfileSecondDerivFormula f t) t := by
  let df : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ f
  let ddf : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ df
  have hf : HasDerivAt (fun x : ℝ => f x)
      (df (Real.exp (-t))) (Real.exp (-t)) := by
    simpa [df, SchwartzMap.derivCLM_apply] using
      (f.differentiableAt.hasDerivAt : HasDerivAt (fun x : ℝ => f x)
        (deriv (fun x : ℝ => f x) (Real.exp (-t))) (Real.exp (-t)))
  have hdf : HasDerivAt (fun x : ℝ => df x)
      (ddf (Real.exp (-t))) (Real.exp (-t)) := by
    simpa [ddf, SchwartzMap.derivCLM_apply] using
      (df.differentiableAt.hasDerivAt : HasDerivAt (fun x : ℝ => df x)
        (deriv (fun x : ℝ => df x) (Real.exp (-t))) (Real.exp (-t)))
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) using 1 <;>
      simp [Function.comp_def] <;> ring
  have hfComp : HasDerivAt (fun u : ℝ => f (Real.exp (-u)))
      ((-Real.exp (-t)) • df (Real.exp (-t))) t := by
    simpa [Function.comp_def] using hf.scomp t hexp
  have hdfComp : HasDerivAt (fun u : ℝ => df (Real.exp (-u)))
      ((-Real.exp (-t)) • ddf (Real.exp (-t))) t := by
    simpa [Function.comp_def] using hdf.scomp t hexp
  have ha : HasDerivAt (fun u : ℝ => -Real.exp (-u))
      (Real.exp (-t)) t := by
    simpa [Function.comp_def] using hexp.const_mul (-1 : ℝ)
  have hinner : HasDerivAt
      (fun u : ℝ => (-Real.exp (-u)) • df (Real.exp (-u)))
      (Real.exp (-t) • df (Real.exp (-t)) +
        (-Real.exp (-t)) • ((-Real.exp (-t)) • ddf (Real.exp (-t)))) t := by
    convert ha.smul hdfComp using 1 <;>
      simp [Function.comp_def, Pi.smul_apply, add_comm, add_left_comm,
        add_assoc] <;> ring
  have hweight : HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
      ((-1 / 2 : ℝ) * Real.exp (-t / 2)) t := by
    convert (Real.hasDerivAt_exp (-t / 2)).comp t
      ((hasDerivAt_neg t).div_const 2) using 1 <;> ring
  have hchain := hweight.smul hinner
  have hq : HasDerivAt
      (fun u : ℝ => (-1 / 2 : ℝ) * Real.exp (-u / 2))
      ((1 / 4 : ℝ) * Real.exp (-t / 2)) t := by
    convert hweight.const_mul (-1 / 2 : ℝ) using 1 <;> ring
  have hsecond := hq.smul hfComp
  have hsum := hchain.add hsecond
  convert hsum using 1 <;>
    simp [Function.comp_def, Pi.smul_apply,
      ccm24CriticalMellinLogProfileChainDeriv,
      ccm24CriticalMellinLogProfileSecondDerivFormula, df, ddf,
      add_comm, add_left_comm, add_assoc] <;>
    ring

theorem integrable_ccm24CriticalMellinLogProfileSecondDerivFormula
    (f : SchwartzMap ℝ ℂ) :
    Integrable (ccm24CriticalMellinLogProfileSecondDerivFormula f) volume := by
  let df : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ f
  let ddf : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ df
  let middle : ℝ → ℂ := fun t =>
    (Real.exp (-t / 2) * Real.exp (-t) ^ 2 : ℝ) • ddf (Real.exp (-t))
  have hmiddle_meas : AEStronglyMeasurable middle volume := by
    apply Continuous.aestronglyMeasurable
    unfold middle
    fun_prop
  let C0 : ℝ := SchwartzMap.seminorm ℂ 0 0 ddf
  let C3 : ℝ := SchwartzMap.seminorm ℂ 3 0 ddf
  have hposMajorant : IntegrableOn
      (fun t : ℝ => C0 * Real.exp ((-5 / 2 : ℝ) * t))
      (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := (-5 / 2 : ℝ)) (by norm_num) 0).const_mul C0
  have hpos : IntegrableOn middle (Set.Ioi 0) volume := by
    apply hposMajorant.mono' hmiddle_meas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h0 := SchwartzMap.norm_le_seminorm ℂ ddf (Real.exp (-t))
    simp only [middle, norm_smul, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
      abs_of_pos (Real.exp_pos _)]
    have h0' : ‖ddf (Real.exp (-t))‖ ≤ C0 := by simpa [C0] using h0
    calc
      Real.exp (-t / 2) * Real.exp (-t) ^ 2 * ‖ddf (Real.exp (-t))‖ ≤
      Real.exp (-t / 2) * Real.exp (-t) ^ 2 * C0 := by gcongr
      _ = C0 * Real.exp ((-5 / 2 : ℝ) * t) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        ring
  have hnegMajorant : IntegrableOn
      (fun t : ℝ => C3 * Real.exp ((1 / 2 : ℝ) * t))
      (Set.Iic 0) volume :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0).const_mul C3
  have hneg : IntegrableOn middle (Set.Iic 0) volume := by
    apply hnegMajorant.mono' hmiddle_meas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have h3 := SchwartzMap.norm_pow_mul_le_seminorm ℂ ddf 3 (Real.exp (-t))
    simp only [middle, norm_smul, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
      abs_of_pos (Real.exp_pos _)]
    rw [show -t / 2 = (1 / 2 : ℝ) * t + (-t) by ring,
      show Real.exp (-t) ^ 2 = Real.exp (-2 * t) by
        rw [← Real.exp_nat_mul]; norm_num]
    rw [Real.exp_add]
    have h3' : Real.exp (-t) ^ 3 * ‖ddf (Real.exp (-t))‖ ≤ C3 := by
      simpa [C3, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h3
    have hfactor : Real.exp ((1 / 2 : ℝ) * t) *
        (Real.exp (-t) ^ 3 * ‖ddf (Real.exp (-t))‖) ≤
        Real.exp ((1 / 2 : ℝ) * t) * C3 := by
      gcongr
    have heq : Real.exp (-t) * Real.exp (-2 * t) = Real.exp (-t) ^ 3 := by
      calc
        Real.exp (-t) * Real.exp (-2 * t) =
            Real.exp ((-t) + (-2 * t)) := by rw [Real.exp_add]
        _ = Real.exp ((-t) + (-t) + (-t)) := by congr 1 <;> ring
        _ = Real.exp (-t) ^ 3 := by
          rw [pow_three, Real.exp_add, Real.exp_add]
          ac_rfl
    calc
      Real.exp ((1 / 2 : ℝ) * t) * Real.exp (-t) * Real.exp (-2 * t) *
          ‖ddf (Real.exp (-t))‖ =
          Real.exp ((1 / 2 : ℝ) * t) *
            (Real.exp (-t) ^ 3 * ‖ddf (Real.exp (-t))‖) := by
              simp only [← heq]
              ring
      _ ≤ Real.exp ((1 / 2 : ℝ) * t) * C3 := hfactor
      _ = C3 * Real.exp ((1 / 2 : ℝ) * t) := by ring
  have hmiddle : Integrable middle volume := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hneg.union hpos
  have hchain := integrable_ccm24CriticalMellinLogProfileChainDeriv f
  have hprofile := integrable_ccm24CriticalMellinLogProfile f
  have hsum := (hchain.const_mul (-2 : ℂ)).add
    (hmiddle.add (hprofile.const_mul (1 / 4 : ℂ)))
  apply hsum.congr
  filter_upwards [] with t
  simp only [ccm24CriticalMellinLogProfileSecondDerivFormula,
    ccm24CriticalMellinLogProfileChainDeriv, middle, df, ddf]
  simp [ccm24CriticalMellinLogProfile, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm] <;> ring

theorem integrable_ccm24CriticalMellinLogProfileFirstDerivFormula
    (f : SchwartzMap ℝ ℂ) :
    Integrable (ccm24CriticalMellinLogProfileFirstDerivFormula f) volume := by
  have hchain := integrable_ccm24CriticalMellinLogProfileChainDeriv f
  have hprofile := (integrable_ccm24CriticalMellinLogProfile f).const_mul
    ((-1 / 2 : ℝ) : ℂ)
  have hsum := hchain.add hprofile
  apply hsum.congr
  filter_upwards [] with t
  simp [ccm24CriticalMellinLogProfileFirstDerivFormula,
    ccm24CriticalMellinLogProfile, ccm24CriticalMellinLogProfileChainDeriv,
    smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

theorem differentiable_ccm24CriticalMellinLogProfileFirstDerivFormula
    (f : SchwartzMap ℝ ℂ) :
    Differentiable ℝ (ccm24CriticalMellinLogProfileFirstDerivFormula f) := by
  intro t
  change DifferentiableAt ℝ
    (fun u : ℝ =>
      ccm24CriticalMellinLogProfileChainDeriv f u +
        ((-1 / 2 : ℝ) * Real.exp (-u / 2)) • f (Real.exp (-u))) t
  exact (hasDerivAt_ccm24CriticalMellinLogProfileFirstDeriv_formula f t).differentiableAt

theorem integrable_deriv_ccm24CriticalMellinLogProfileFirstDerivFormula
  (f : SchwartzMap ℝ ℂ) :
    Integrable (deriv (ccm24CriticalMellinLogProfileFirstDerivFormula f)) volume := by
  have hsecond := integrable_ccm24CriticalMellinLogProfileSecondDerivFormula f
  apply hsecond.congr
  filter_upwards [] with t
  change ccm24CriticalMellinLogProfileSecondDerivFormula f t =
    deriv (fun u : ℝ =>
      ccm24CriticalMellinLogProfileChainDeriv f u +
        ((-1 / 2 : ℝ) * Real.exp (-u / 2)) • f (Real.exp (-u))) t
  rw [(hasDerivAt_ccm24CriticalMellinLogProfileFirstDeriv_formula f t).deriv]

theorem memLp_two_fourier_ccm24CriticalMellinLogProfileFirstDerivFormula
    (f : SchwartzMap ℝ ℂ) :
    MemLp (𝓕 (ccm24CriticalMellinLogProfileFirstDerivFormula f)) 2 volume :=
  memLp_two_fourier_of_integrable_deriv
    (ccm24CriticalMellinLogProfileFirstDerivFormula f)
    (integrable_ccm24CriticalMellinLogProfileFirstDerivFormula f)
    (differentiable_ccm24CriticalMellinLogProfileFirstDerivFormula f)
    (integrable_deriv_ccm24CriticalMellinLogProfileFirstDerivFormula f)

end Dev
end ConnesWeilRH
