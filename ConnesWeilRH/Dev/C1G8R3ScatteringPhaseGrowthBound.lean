/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseGrowth

/-!
# Linear growth of the actual archimedean scattering-phase derivative

The unit-modulus quotient cancels the GammaR factor norm in the exact phase
derivative formula.  The preceding GammaR-log growth estimate therefore
transfers directly to the phase derivative.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open scoped ComplexConjugate

theorem norm_deriv_ccm24ArchimedeanScatteringPhase_le_linear (xi : ℝ) :
    ‖deriv ccm24ArchimedeanScatteringPhase xi‖ ≤
      4 * Real.pi *
        (‖ccm24CriticalGammaRLogDeriv 0‖ +
          (18 * Real.pi) * |xi|) := by
  let F : ℝ → ℂ := ccm24ArchimedeanFactor
  let L : ℝ → ℂ := ccm24CriticalGammaRLogDeriv
  let a : ℂ := -Complex.I * (2 * Real.pi : ℂ)
  have hF0 : F xi ≠ 0 := by
    simpa [F] using ccm24ArchimedeanFactor_ne_zero xi
  have hphase := deriv_ccm24ArchimedeanScatteringPhase_formula xi
  have hF' := (hasDerivAt_ccm24ArchimedeanFactor_logDeriv xi).deriv
  have hrewrite :
      (deriv F xi * conj (F xi) - F xi * conj (deriv F xi)) /
          (conj (F xi)) ^ 2 =
      (F xi / conj (F xi)) *
          (a * L xi - conj (a * L xi)) := by
    rw [hF']
    simp [F, L, a, map_mul, map_neg, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hF0]
  rw [show deriv ccm24ArchimedeanScatteringPhase xi =
      (deriv F xi * conj (F xi) - F xi * conj (deriv F xi)) /
        (conj (F xi)) ^ 2 by simpa [F] using hphase]
  rw [hrewrite, norm_mul]
  have hnormPhase : ‖F xi / conj (F xi)‖ = 1 := by
    rw [norm_div, Complex.norm_conj]
    exact div_self (norm_ne_zero_iff.mpr hF0)
  rw [hnormPhase, one_mul]
  have hdiff : ‖a * L xi - conj (a * L xi)‖ ≤
      2 * ‖a‖ * ‖L xi‖ := by
    calc
      ‖a * L xi - conj (a * L xi)‖ ≤
          ‖a * L xi‖ + ‖conj (a * L xi)‖ := norm_sub_le _ _
      _ = 2 * ‖a‖ * ‖L xi‖ := by
        rw [Complex.norm_conj, norm_mul]
        ring
  have ha : ‖a‖ = 2 * Real.pi := by
    simp [a, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hL := norm_ccm24CriticalGammaRLogDeriv_le_linear xi
  calc
    ‖a * L xi - conj (a * L xi)‖ ≤ 2 * ‖a‖ * ‖L xi‖ := hdiff
    _ = 4 * Real.pi * ‖L xi‖ := by rw [ha]; ring
    _ ≤ 4 * Real.pi *
          (‖ccm24CriticalGammaRLogDeriv 0‖ +
            (18 * Real.pi) * |xi|) := by
      apply mul_le_mul_of_nonneg_left hL
      positivity

end Dev
end ConnesWeilRH
