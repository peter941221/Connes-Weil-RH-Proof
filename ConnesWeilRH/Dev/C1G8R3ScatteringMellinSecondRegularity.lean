/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseDigamma
import ConnesWeilRH.Dev.C1G8R3CriticalMellinSecondDerivative

/-!
# Second-order product interface for the scattering-weighted Mellin profile

This leaf combines the actual archimedean scattering phase with the concrete
critical Mellin profile.  It records the exact second derivative needed by
the annular two-IBP consumer; the separate L1 estimate for its four product
terms remains an analytic obligation.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete

theorem differentiable_deriv_ccm24ScatteringMellinProfile
    (f : SchwartzMap ℝ ℂ) :
    Differentiable ℝ (deriv (fun t : ℝ =>
      ccm24ArchimedeanScatteringPhase t *
        ccm24CriticalMellinLogProfile f t)) := by
  intro xi
  have hphase : HasDerivAt ccm24ArchimedeanScatteringPhase
      (deriv ccm24ArchimedeanScatteringPhase xi) xi :=
    (differentiable_ccm24ArchimedeanScatteringPhase xi).hasDerivAt
  have hphase2 : HasDerivAt (deriv ccm24ArchimedeanScatteringPhase)
      (deriv (deriv ccm24ArchimedeanScatteringPhase) xi) xi :=
    (differentiable_ccm24ArchimedeanScatteringPhase_deriv xi).hasDerivAt
  have hprofile : HasDerivAt (ccm24CriticalMellinLogProfile f)
      (deriv (ccm24CriticalMellinLogProfile f) xi) xi :=
    (differentiable_ccm24CriticalMellinLogProfile f xi).hasDerivAt
  have hprofile2 : HasDerivAt
      (deriv (ccm24CriticalMellinLogProfile f))
      (deriv (deriv (ccm24CriticalMellinLogProfile f)) xi) xi := by
    have hprofile_fun :
        deriv (ccm24CriticalMellinLogProfile f) =
          ccm24CriticalMellinLogProfileFirstDerivFormula f := by
      funext t
      simpa [ccm24CriticalMellinLogProfileFirstDerivFormula] using
        (hasDerivAt_ccm24CriticalMellinLogProfile f t).deriv
    have h := hasDerivAt_ccm24CriticalMellinLogProfileFirstDeriv_formula f xi
    have hformula :
        (fun u : ℝ =>
          ccm24CriticalMellinLogProfileChainDeriv f u +
            ((-1 / 2 : ℝ) * Real.exp (-u / 2)) • f (Real.exp (-u))) =
          ccm24CriticalMellinLogProfileFirstDerivFormula f := by
      funext u
      simp [ccm24CriticalMellinLogProfileFirstDerivFormula, smul_eq_mul]
    have hderiv_first :
        deriv (ccm24CriticalMellinLogProfileFirstDerivFormula f) xi =
          ccm24CriticalMellinLogProfileSecondDerivFormula f xi := by
      rw [← hformula]
      exact h.deriv
    rw [hprofile_fun]
    rw [hderiv_first]
    rw [← hformula]
    exact h
  have hfirst := hphase.mul hprofile
  have hfirst_fun :
      (fun t : ℝ => deriv (fun u : ℝ =>
        ccm24ArchimedeanScatteringPhase u *
          ccm24CriticalMellinLogProfile f u) t) =
      (fun t : ℝ =>
        deriv ccm24ArchimedeanScatteringPhase t *
            ccm24CriticalMellinLogProfile f t +
          ccm24ArchimedeanScatteringPhase t *
            deriv (ccm24CriticalMellinLogProfile f) t) := by
    funext t
    simpa using (differentiable_ccm24ArchimedeanScatteringPhase t).hasDerivAt.mul
      (differentiable_ccm24CriticalMellinLogProfile f t).hasDerivAt |>.deriv
  change DifferentiableAt ℝ (fun t : ℝ => deriv (fun u : ℝ =>
    ccm24ArchimedeanScatteringPhase u *
      ccm24CriticalMellinLogProfile f u) t) xi
  rw [hfirst_fun]
  exact (hphase2.mul hprofile).add (hphase.mul hprofile2) |>.differentiableAt

end Dev
end ConnesWeilRH
