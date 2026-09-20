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

end Dev
end ConnesWeilRH
