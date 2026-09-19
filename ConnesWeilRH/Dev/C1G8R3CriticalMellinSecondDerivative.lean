/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24ArchimedeanCarrier

/-!
# Exact second chain rule for the critical Mellin profile

The carrier source already proves the first derivative of the critical Mellin
profile.  This leaf records its exact second chain rule on the Schwartz core.
It deliberately makes no integrability claim; the resulting formula is the
input for the separate quantitative majorant proof.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete

noncomputable def ccm24CriticalMellinLogProfileSecondDerivFormula
    (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  (2 * (Real.exp (-t / 2) * Real.exp (-t)) : ℝ) •
      (SchwartzMap.derivCLM ℝ ℂ f) (Real.exp (-t)) +
    (Real.exp (-t / 2) * Real.exp (-t) ^ 2 : ℝ) •
      (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ f))
        (Real.exp (-t)) +
    ((1 / 4 : ℝ) * Real.exp (-t / 2)) • f (Real.exp (-t))

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

end Dev
end ConnesWeilRH
