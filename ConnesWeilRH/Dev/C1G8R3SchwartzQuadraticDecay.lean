/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3HardyTailRate

/-!
# Schwartz-core quadratic Fourier decay

The Hardy-tail consumer needs a quantitative square-summable tail.  This
module supplies the regularity bridge on the genuine Schwartz core: the
Schwartz derivative operator provides the integrability and differentiability
instances required by the two integrations-by-parts estimate.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open scoped FourierTransform

theorem fourier_norm_mul_sq_le_schwartz_second_deriv
    (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖x‖ ^ 2 * ‖𝓕 g x‖ ≤
      ∫ t : ℝ, ‖deriv (deriv (g : ℝ → ℂ)) t‖ ∂volume := by
  have hg : Integrable (g : ℝ → ℂ) volume := g.integrable
  have hgDiff : Differentiable ℝ (g : ℝ → ℂ) := g.differentiable
  have hgDeriv : Integrable (deriv (g : ℝ → ℂ)) volume := by
    simpa only [SchwartzMap.derivCLM_apply] using
      (SchwartzMap.derivCLM ℝ ℂ g).integrable
  have hderivDiff : Differentiable ℝ (deriv (g : ℝ → ℂ)) := by
    have h := (SchwartzMap.derivCLM ℝ ℂ g).differentiable
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hsecond : Integrable (deriv (deriv (g : ℝ → ℂ))) volume := by
    have h : Integrable
        ((SchwartzMap.derivCLM ℝ ℂ
          (SchwartzMap.derivCLM ℝ ℂ g) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (volume : Measure ℝ) :=
      (SchwartzMap.derivCLM ℝ ℂ
        (SchwartzMap.derivCLM ℝ ℂ g)).integrable
    simpa only [SchwartzMap.derivCLM_apply] using h
  exact fourier_norm_mul_sq_le_integral_norm_second_deriv
    (g := (g : ℝ → ℂ)) hg hgDiff hgDeriv hderivDiff hsecond x

theorem summable_schwartz_fourier_normSq_on_unit_annuli
    (g : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ =>
      ‖𝓕 g (n : ℝ)‖ ^ 2) := by
  let C : ℝ := ∫ t : ℝ, ‖deriv (deriv (g : ℝ → ℂ)) t‖ ∂volume
  have hC : 0 ≤ C := by
    dsimp [C]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hshift : Summable (fun n : ℕ =>
      ‖𝓕 g ((n + 1 : ℕ) : ℝ)‖ ^ 2) := by
    apply summable_normSq_of_quadratic_decay
      (u := fun n : ℕ => 𝓕 g ((n + 1 : ℕ) : ℝ)) hC
    intro n
    have hdecay := fourier_norm_mul_sq_le_schwartz_second_deriv g
      ((n + 1 : ℕ) : ℝ)
    dsimp [C]
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hscale :
        (((n + 1 : ℕ) : ℝ) ^ 2) *
          ‖𝓕 g ((n + 1 : ℕ) : ℝ)‖ ≤ C := by
      have hnorm : ‖((n + 1 : ℕ) : ℝ)‖ = ((n + 1 : ℕ) : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact Nat.cast_nonneg _
      rw [hnorm] at hdecay
      simpa only [C] using hdecay
    have hpos : 0 < (((n + 1 : ℕ) : ℝ) ^ (2 : ℝ)) := by positivity
    have hscale' :
        ‖𝓕 g ((n + 1 : ℕ) : ℝ)‖ *
          (((n + 1 : ℕ) : ℝ) ^ (2 : ℝ)) ≤ C := by
      simpa [Real.rpow_natCast, mul_comm] using hscale
    have hquot := (le_div_iff₀ hpos).2 hscale'
    simpa [div_eq_mul_inv, Real.rpow_neg (le_of_lt hn)] using hquot
  apply (summable_nat_add_iff
    (f := fun n : ℕ => ‖𝓕 g (n : ℝ)‖ ^ 2) 1).mp
  simpa [Nat.cast_add, Nat.cast_one] using hshift

end Dev
end ConnesWeilRH
