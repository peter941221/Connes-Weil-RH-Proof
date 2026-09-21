/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseDigamma

/-!
# Uniform derivative bound for the critical GammaR logarithmic derivative

The quarter-line digamma derivative series gives a concrete global bound for
the real-frequency derivative of the GammaR logarithmic derivative.  This is
the first quantitative growth input for the scattering-weighted Mellin L1
consumer.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open scoped ComplexConjugate

theorem norm_deriv_ccm24CriticalGammaRLogDeriv_le (xi : ℝ) :
    ‖deriv ccm24CriticalGammaRLogDeriv xi‖ ≤ 18 * Real.pi := by
  let z : ℂ := (1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ)
  have hz : (1 / 4 : ℝ) < (z + 1).re := by
    simp [z, Complex.add_re]
  have hquarter := (hasDerivAt_digamma_criticalQuarterLine xi).deriv
  have hquarterNorm : ‖deriv Complex.digamma z‖ ≤ 36 := by
    rw [show z = (1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ) by rfl,
      hquarter]
    calc
      ‖deriv Complex.digamma
            ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ) + 1) +
          (((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))⁻¹) ^ (2 : ℕ)‖ ≤
          ‖deriv Complex.digamma
              ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ) + 1)‖ +
            ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))⁻¹ ^ (2 : ℕ)‖ :=
        norm_add_le _ _
      _ ≤ 20 + 16 := by
        apply add_le_add
        · exact norm_digamma_deriv_le_twenty (by
            change (1 / 4 : ℝ) < (z + 1).re
            exact hz)
        · have hnorm :
              ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))‖ ≥ 1 / 4 := by
            have hre :
                1 / 4 ≤ ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ)).re := by
              simp [Complex.mul_re]
            exact hre.trans (le_trans (le_abs_self _)
              (Complex.abs_re_le_norm _))
          have hpow :
              ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))⁻¹ ^ (2 : ℕ)‖ =
                ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))‖⁻¹ ^ (2 : ℕ) := by
            rw [norm_pow, norm_inv]
          rw [hpow]
          have hnonneg :
              0 ≤ ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))‖⁻¹ :=
            inv_nonneg.mpr (norm_nonneg _)
          have hinv :
              ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))‖⁻¹ ≤ 4 := by
            have hpos :
                0 < ‖((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ))‖ :=
              lt_of_lt_of_le (by norm_num) hnorm
            apply (inv_le_iff_one_le_mul₀ hpos).2
            nlinarith [hnorm]
          have hsq := (sq_le_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 4)).2 hinv
          nlinarith [hsq]
      _ ≤ 36 := by norm_num
  have hderiv := (hasDerivAt_ccm24CriticalGammaRLogDeriv xi).deriv
  rw [hderiv]
  have hnorm := norm_mul_le
    ((-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ))
    (deriv Complex.digamma z)
  have hscale :
      ‖((-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ))‖ = Real.pi / 2 := by
    simp [norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hscale] at hnorm
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  calc
    ‖((-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ)) *
        deriv Complex.digamma z‖ ≤
        (Real.pi / 2) * ‖deriv Complex.digamma z‖ := hnorm
    _ ≤ (Real.pi / 2) * 36 :=
      mul_le_mul_of_nonneg_left hquarterNorm (by positivity)
    _ = 18 * Real.pi := by ring

end Dev
end ConnesWeilRH
