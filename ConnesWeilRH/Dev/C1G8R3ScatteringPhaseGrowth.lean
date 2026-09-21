/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseDerivativeBound

/-!
# Linear growth of the critical GammaR logarithmic derivative

The uniform derivative bound is integrated with Mathlib's interval mean-value
estimate.  This produces the polynomial growth input needed before the
scattering-phase product can be shown L1 against the Mellin profile.
-/

namespace ConnesWeilRH
namespace Dev

open Set

theorem norm_ccm24CriticalGammaRLogDeriv_le_linear (xi : ℝ) :
    ‖ccm24CriticalGammaRLogDeriv xi‖ ≤
      ‖ccm24CriticalGammaRLogDeriv 0‖ + (18 * Real.pi) * |xi| := by
  let L : ℝ → ℂ := ccm24CriticalGammaRLogDeriv
  have hdiff : Differentiable ℝ L := by
    intro x
    simpa [L] using (hasDerivAt_ccm24CriticalGammaRLogDeriv x).differentiableAt
  have hcont : ContinuousOn L (Icc (0 : ℝ) xi) := by
    exact hdiff.continuous.continuousOn
  have hright : ∀ x ∈ Ico (0 : ℝ) xi,
      HasDerivWithinAt L (deriv L x) (Ici x) x := by
    intro x hx
    have hdx := hasDerivAt_ccm24CriticalGammaRLogDeriv x
    have heq : deriv L x =
        (-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ) *
          deriv Complex.digamma
            ((1 / 4 : ℂ) - Complex.I * (Real.pi * x : ℝ)) := by
      simpa [L] using hdx.deriv
    rw [heq]
    simpa [L] using hdx.hasDerivWithinAt
  have hbound : ∀ x ∈ Ico (0 : ℝ) xi,
      ‖deriv L x‖ ≤ 18 * Real.pi := by
    intro x hx
    simpa [L] using norm_deriv_ccm24CriticalGammaRLogDeriv_le x
  by_cases hxi : 0 ≤ xi
  · have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      (a := (0 : ℝ)) (b := xi) hcont hright hbound xi
      (right_mem_Icc.mpr hxi)
    have htriangle : ‖L xi‖ ≤ ‖L xi - L 0‖ + ‖L 0‖ := by
      calc
        ‖L xi‖ = ‖(L xi - L 0) + L 0‖ := by ring_nf
        _ ≤ ‖L xi - L 0‖ + ‖L 0‖ := norm_add_le _ _
    calc
      ‖ccm24CriticalGammaRLogDeriv xi‖ = ‖L xi‖ := by rfl
      _ ≤ ‖L xi - L 0‖ + ‖L 0‖ := htriangle
      _ ≤ (18 * Real.pi) * (xi - 0) + ‖L 0‖ :=
        by
          have h := add_le_add_right hseg ‖L 0‖
          simpa [add_comm, add_left_comm, add_assoc] using h
      _ = ‖ccm24CriticalGammaRLogDeriv 0‖ + (18 * Real.pi) * |xi| := by
        rw [abs_of_nonneg hxi]
        simp [L]
        ring
  · have hxi' : xi ≤ 0 := le_of_not_ge hxi
    have hcont' : ContinuousOn L (Icc xi (0 : ℝ)) := by
      exact hdiff.continuous.continuousOn
    have hright' : ∀ x ∈ Ico xi (0 : ℝ),
        HasDerivWithinAt L (deriv L x) (Ici x) x := by
      intro x hx
      have hdx := hasDerivAt_ccm24CriticalGammaRLogDeriv x
      have heq : deriv L x =
          (-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ) *
            deriv Complex.digamma
              ((1 / 4 : ℂ) - Complex.I * (Real.pi * x : ℝ)) := by
        simpa [L] using hdx.deriv
      rw [heq]
      simpa [L] using hdx.hasDerivWithinAt
    have hbound' : ∀ x ∈ Ico xi (0 : ℝ),
        ‖deriv L x‖ ≤ 18 * Real.pi := by
      intro x hx
      simpa [L] using norm_deriv_ccm24CriticalGammaRLogDeriv_le x
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      (a := xi) (b := (0 : ℝ)) hcont' hright' hbound' 0
      (right_mem_Icc.mpr hxi')
    have htriangle : ‖L xi‖ ≤ ‖L 0 - L xi‖ + ‖L 0‖ := by
      calc
        ‖L xi‖ = ‖-(L 0 - L xi) + L 0‖ := by ring_nf
        _ ≤ ‖-(L 0 - L xi)‖ + ‖L 0‖ := norm_add_le _ _
        _ = ‖L 0 - L xi‖ + ‖L 0‖ := by rw [norm_neg]
    calc
      ‖ccm24CriticalGammaRLogDeriv xi‖ = ‖L xi‖ := by rfl
      _ ≤ ‖L 0 - L xi‖ + ‖L 0‖ := htriangle
      _ ≤ (18 * Real.pi) * (0 - xi) + ‖L 0‖ :=
        by
          have h := add_le_add_right hseg ‖L 0‖
          simpa [add_comm, add_left_comm, add_assoc] using h
      _ = ‖ccm24CriticalGammaRLogDeriv 0‖ + (18 * Real.pi) * |xi| := by
        rw [abs_of_nonpos hxi']
        simp [L]
        ring

end Dev
end ConnesWeilRH
