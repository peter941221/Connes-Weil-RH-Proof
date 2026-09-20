/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1DigammaDerivativeSeries
import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseRegularity

/-!
# Digamma readback for the archimedean scattering line

The GammaR logarithmic derivative on the CCM24 critical line is rewritten as
the explicit digamma expression already controlled on `Re = 1/4`.  This is
the local analytic interface needed before differentiating the scattering
phase a second time.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Filter Topology
open scoped Topology

noncomputable def ccm24CriticalGammaRLogDeriv (xi : ℝ) : ℂ :=
  logDeriv Complex.Gammaℝ
    ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ))

theorem ccm24CriticalGammaRLogDeriv_eq_digamma (xi : ℝ) :
    ccm24CriticalGammaRLogDeriv xi =
      -((Complex.log (Real.pi : ℂ)) / 2) +
        (1 / 2 : ℂ) *
          Complex.digamma ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ)) := by
  unfold ccm24CriticalGammaRLogDeriv
  have h := Source.C1XiCenterTwoGamma.logDeriv_GammaR_eq_log_pi_add_digamma
    (s := ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ))) (by
      simp [Complex.mul_re])
  have harg :
      ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ)) / 2 =
        (1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ) := by
    push_cast
    ring
  rw [harg] at h
  convert h using 1 <;> ring

theorem hasDerivAt_digamma_criticalQuarterLine (xi : ℝ) :
    HasDerivAt Complex.digamma
      (deriv Complex.digamma
          ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ) + 1) +
        (((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))⁻¹) ^ (2 : ℕ))
      ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ)) := by
  let z : ℂ := (1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ)
  have hzpos : 0 < z.re := by simp [z, Complex.mul_re]
  have hd := hasDerivAt_digamma_of_re_ge_quarter (z := z + 1) (by
    change (1 / 4 : ℝ) < (z + 1).re
    simp [z, Complex.mul_re])
  have hcomp := hd.comp z ((hasDerivAt_id z).add_const 1)
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [z, Complex.mul_re] at this
  have hinv := (hasDerivAt_id z).inv hz
  have hright := hcomp.sub hinv
  have hposEvent : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzpos
  have heq : (fun w : ℂ => Complex.digamma w) =ᶠ[𝓝 z]
      (fun w : ℂ => Complex.digamma (w + 1) - w⁻¹) := by
    filter_upwards [hposEvent] with w hw
    have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := by
      intro m h
      have hreal := congrArg Complex.re h
      simp at hreal
      linarith
    rw [Complex.digamma_apply_add_one w hne]
    ring
  have hfinal := hright.congr_of_eventuallyEq heq
  have hderiv := hd.deriv
  rw [← hderiv] at hfinal
  simpa [z, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfinal

theorem hasDerivAt_ccm24CriticalGammaRLogDeriv (xi : ℝ) :
    HasDerivAt ccm24CriticalGammaRLogDeriv
      ((-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ) *
        deriv Complex.digamma
          ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))) xi := by
  let z : ℝ → ℂ := fun x =>
    (1 / 4 : ℂ) - Complex.I * (Real.pi * x : ℝ)
  have hz : HasDerivAt z (-Complex.I * (Real.pi : ℂ)) xi := by
    let a : ℂ := -Complex.I * (Real.pi : ℂ)
    have hlin : HasDerivAt (fun x : ℝ => a * (x : ℂ)) a xi := by
      simpa using ((hasDerivAt_id (xi : ℂ)).const_mul a).comp_ofReal
    have hsum := (hasDerivAt_const (x := xi) (c := (1 / 4 : ℂ))).add hlin
    convert hsum using 1
    · funext x
      simp [z, a]
      ring
    · simpa [a]
  have hd := hasDerivAt_digamma_criticalQuarterLine xi
  have hfd := hd.complexToReal_fderiv.comp_hasDerivAt xi hz
  have hderiv := hd.deriv
  have hcomp : HasDerivAt (fun x : ℝ => Complex.digamma (z x))
      (deriv Complex.digamma (z xi) * (-Complex.I * (Real.pi : ℂ))) xi := by
    rw [← hderiv] at hfd
    simpa [Function.comp_def, z, div_eq_mul_inv, inv_pow,
      mul_comm, mul_left_comm, mul_assoc] using hfd
  have hscaled := hcomp.const_mul (1 / 2 : ℂ)
  have hfun : ccm24CriticalGammaRLogDeriv = fun x : ℝ =>
      -((Complex.log (Real.pi : ℂ)) / 2) +
        (1 / 2 : ℂ) * Complex.digamma (z x) := by
    funext x
    simpa [z] using ccm24CriticalGammaRLogDeriv_eq_digamma x
  rw [hfun]
  simpa [z, mul_comm, mul_left_comm, mul_assoc] using
    hscaled.add_const (-((Complex.log (Real.pi : ℂ)) / 2))

end Dev
end ConnesWeilRH
