/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20ConcreteTestSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.MellinInversion

/-!
# Mellin tail bounds for fixed-window CC20 tests

This module expresses a positive-variable Mellin transform as the Fourier
transform of a compactly supported logarithmic slice. Schwartz decay then
gives the quadratic vertical-line bound needed by the source Yoshida tail
argument.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaTail

open MeasureTheory
open scoped FourierTransform ContDiff

noncomputable def mellinLogSliceRaw
    (g : TestFunction) (sigma u : ℝ) : ℂ :=
  Real.exp (-sigma * u) • g (Real.exp (-u))

theorem mellinLogSliceRaw_contDiff
    (g : TestFunction) (sigma : ℝ) :
    ContDiff ℝ ∞ (mellinLogSliceRaw g sigma) := by
  unfold mellinLogSliceRaw
  fun_prop

noncomputable def mellinLogSliceJoint (g : TestFunction) (p : ℝ × ℝ) : ℂ :=
  Real.exp (-p.1 * p.2) • g (Real.exp (-p.2))

theorem mellinLogSliceJoint_contDiff (g : TestFunction) :
    ContDiff ℝ ∞ (mellinLogSliceJoint g) := by
  unfold mellinLogSliceJoint
  fun_prop

noncomputable def mellinLogRadius (a b : ℝ) : ℝ :=
  max ‖Real.log a‖ ‖Real.log b‖

theorem mellinLogRadius_nonneg (a b : ℝ) :
    0 ≤ mellinLogRadius a b := by
  exact le_trans (norm_nonneg _) (le_max_left _ _)

theorem mellinLogInterval_subset_radius (a b : ℝ) :
    Set.Ioo (-Real.log b) (-Real.log a) ⊆
      Set.Icc (-mellinLogRadius a b) (mellinLogRadius a b) := by
  intro u hu
  constructor
  · have hlog : Real.log b ≤ ‖Real.log b‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    have hmax : ‖Real.log b‖ ≤ mellinLogRadius a b := le_max_right _ _
    linarith [hu.1]
  · have hlog : -Real.log a ≤ ‖Real.log a‖ := by
      rw [Real.norm_eq_abs]
      exact neg_le_abs _
    have hmax : ‖Real.log a‖ ≤ mellinLogRadius a b := le_max_left _ _
    linarith [hu.2]

theorem mellinLogSliceRaw_support_subset
    (g : TestFunction) (sigma : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    Function.support (mellinLogSliceRaw g sigma) ⊆
      Set.Ioo (-Real.log b) (-Real.log a) := by
  intro u hu
  have hsource : Real.exp (-u) ∈ Function.support g := by
    rw [Function.mem_support] at hu ⊢
    intro hzero
    apply hu
    simp [mellinLogSliceRaw, hzero]
  have hwindow := hsupport hsource
  have hlower : Real.log a < -u :=
    (Real.log_lt_iff_lt_exp ha).2 hwindow.1
  have hupper : -u < Real.log b :=
    (Real.lt_log_iff_exp_lt hb).2 hwindow.2
  constructor <;> linarith

noncomputable def mellinLogSlice
    (g : TestFunction) (sigma : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) : TestFunction := by
  have hsubset :=
    mellinLogSliceRaw_support_subset g sigma ha hb hsupport
  have hcompact : HasCompactSupport (mellinLogSliceRaw g sigma) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (hsubset.trans Set.Ioo_subset_Icc_self)
  exact hcompact.toSchwartzMap (mellinLogSliceRaw_contDiff g sigma)

@[simp] theorem mellinLogSlice_apply
    (g : TestFunction) (sigma : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) (u : ℝ) :
    mellinLogSlice g sigma ha hb hsupport u =
      Real.exp (-sigma * u) • g (Real.exp (-u)) :=
  rfl

theorem mellin_eq_fourier_mellinLogSlice
    (g : TestFunction) (sigma t : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    mellin (fun x : ℝ => g x) ((sigma : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (mellinLogSlice g sigma ha hb hsupport) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  have hfrequency :
      (((sigma : ℂ) + (t : ℂ) * Complex.I).im / (2 * Real.pi)) =
        t / (2 * Real.pi) := by
    simp
  rw [hfrequency]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * Real.pi)))
  funext u
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one,
    sub_zero, add_zero]
  rfl

/-- On each fixed real Mellin line, a compact-window test has quadratic decay
in the Fourier-scaled imaginary coordinate. -/
theorem mellin_vertical_quadratic_decay
    (g : TestFunction) (sigma t : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖mellin (fun x : ℝ => g x)
          ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      SchwartzMap.seminorm ℝ 2 0
        (𝓕 (mellinLogSlice g sigma ha hb hsupport)) := by
  rw [mellin_eq_fourier_mellinLogSlice g sigma t ha hb hsupport]
  exact SchwartzMap.norm_pow_mul_le_seminorm ℝ
    (𝓕 (mellinLogSlice g sigma ha hb hsupport)) 2
    (t / (2 * Real.pi))

theorem mellinLogSliceRaw_iteratedFDeriv_eq_joint_comp
    (g : TestFunction) (sigma u : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (mellinLogSliceRaw g sigma) u =
      (iteratedFDeriv ℝ n (mellinLogSliceJoint g) (sigma, u)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ ℝ) := by
  let L : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  have hraw : mellinLogSliceRaw g sigma =
      (fun z : ℝ × ℝ => mellinLogSliceJoint g ((sigma, 0) + z)) ∘ L := by
    funext x
    simp [mellinLogSliceRaw, mellinLogSliceJoint, L]
  rw [hraw]
  have hcomp := L.iteratedFDeriv_comp_right
    (f := fun z : ℝ × ℝ => mellinLogSliceJoint g ((sigma, 0) + z))
    ((mellinLogSliceJoint_contDiff g).comp (by fun_prop)) u
    (i := n) (mod_cast le_top)
  rw [hcomp]
  rw [iteratedFDeriv_comp_add_left]
  simp [L]

theorem continuous_norm_mellinLogSliceRaw_iteratedFDeriv
    (g : TestFunction) (n : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ n (mellinLogSliceRaw g p.1) p.2‖ := by
  have hderiv : Continuous (iteratedFDeriv ℝ n (mellinLogSliceJoint g)) :=
    (mellinLogSliceJoint_contDiff g).continuous_iteratedFDeriv (mod_cast le_top)
  have hcomp : Continuous fun p : ℝ × ℝ =>
      (iteratedFDeriv ℝ n (mellinLogSliceJoint g) p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    fun_prop
  convert hcomp.norm using 1
  funext p
  rw [mellinLogSliceRaw_iteratedFDeriv_eq_joint_comp]

theorem mellinLogSliceRaw_tsupport_subset_radius
    (g : TestFunction) (sigma a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    tsupport (mellinLogSliceRaw g sigma) ⊆
      Set.Icc (-mellinLogRadius a b) (mellinLogRadius a b) := by
  apply closure_minimal
  · exact (mellinLogSliceRaw_support_subset g sigma ha hb hsupport).trans
      (mellinLogInterval_subset_radius a b)
  · exact isClosed_Icc

theorem mellinLogSliceRaw_iteratedFDeriv_eq_zero_of_not_mem_radius
    (g : TestFunction) (sigma a b u : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b)
    (hu : u ∉ Set.Icc (-mellinLogRadius a b) (mellinLogRadius a b)) :
    iteratedFDeriv ℝ n (mellinLogSliceRaw g sigma) u = 0 := by
  by_contra hne
  have husupport : u ∈ Function.support
      (iteratedFDeriv ℝ n (mellinLogSliceRaw g sigma)) := by
    rw [Function.mem_support]
    exact hne
  apply hu
  exact mellinLogSliceRaw_tsupport_subset_radius g sigma a b ha hb hsupport
    (support_iteratedFDeriv_subset n husupport)

theorem continuousOn_mellinLogSliceRaw_iteratedFDeriv_integral
    (g : TestFunction) (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    ContinuousOn
      (fun sigma : ℝ => ∫ u : ℝ,
        ‖iteratedFDeriv ℝ n (mellinLogSliceRaw g sigma) u‖)
      (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_integral_of_compact_support isCompact_Icc
  · exact (continuous_norm_mellinLogSliceRaw_iteratedFDeriv g n).continuousOn
  · intro sigma u _hsigma hu
    rw [norm_eq_zero]
    exact mellinLogSliceRaw_iteratedFDeriv_eq_zero_of_not_mem_radius
      g sigma a b u n ha hb hsupport hu

theorem exists_uniform_mellinLogSliceRaw_iteratedFDeriv_integral_bound
    (g : TestFunction) (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1,
        (∫ u : ℝ, ‖iteratedFDeriv ℝ n (mellinLogSliceRaw g sigma) u‖) ≤ C := by
  have hcontinuous :=
    continuousOn_mellinLogSliceRaw_iteratedFDeriv_integral g a b n ha hb hsupport
  obtain ⟨sigma, hsigma, hsigmaMax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty by exact ⟨0, le_rfl, zero_le_one⟩)
    hcontinuous
  refine ⟨∫ u : ℝ, ‖iteratedFDeriv ℝ n (mellinLogSliceRaw g sigma) u‖,
    integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro sigma' hsigma'
  exact hsigmaMax hsigma'

theorem fourier_mellinLogSlice_quadratic_decay_le_integrals
    (g : TestFunction) (sigma w : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    ‖w‖ ^ 2 * ‖𝓕 (mellinLogSlice g sigma ha hb hsupport) w‖ ≤
      4 * ((∫ u : ℝ, ‖iteratedFDeriv ℝ 0 (mellinLogSliceRaw g sigma) u‖) +
        (∫ u : ℝ, ‖iteratedFDeriv ℝ 1 (mellinLogSliceRaw g sigma) u‖) +
        (∫ u : ℝ, ‖iteratedFDeriv ℝ 2 (mellinLogSliceRaw g sigma) u‖)) := by
  have hfourier := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (f := mellinLogSliceRaw g sigma)
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    (mellinLogSliceRaw_contDiff g sigma)
    (fun k n _hk _hn => by
      simpa only [mellinLogSlice_apply] using
        SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
          (mellinLogSlice g sigma ha hb hsupport) k n)
    (k := 0) (n := 2) le_rfl le_top w
  rw [SchwartzMap.fourier_coe]
  norm_num [Finset.sum_range_succ] at hfourier ⊢
  convert hfourier using 1
  all_goals simp [mellinLogSliceRaw]

/-- A compact-window test has one quadratic Mellin decay constant on the full
closed critical strip. -/
theorem exists_uniform_mellin_vertical_quadratic_decay
    (g : TestFunction)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support g ⊆ Set.Ioo a b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖mellin (fun x : ℝ => g x)
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C0, hC0, hbound0⟩ :=
    exists_uniform_mellinLogSliceRaw_iteratedFDeriv_integral_bound
      g a b 0 ha hb hsupport
  obtain ⟨C1, hC1, hbound1⟩ :=
    exists_uniform_mellinLogSliceRaw_iteratedFDeriv_integral_bound
      g a b 1 ha hb hsupport
  obtain ⟨C2, hC2, hbound2⟩ :=
    exists_uniform_mellinLogSliceRaw_iteratedFDeriv_integral_bound
      g a b 2 ha hb hsupport
  refine ⟨4 * (C0 + C1 + C2), by positivity, ?_⟩
  intro sigma hsigma t
  rw [mellin_eq_fourier_mellinLogSlice g sigma t ha hb hsupport]
  apply (fourier_mellinLogSlice_quadratic_decay_le_integrals
    g sigma (t / (2 * Real.pi)) ha hb hsupport).trans
  gcongr
  · exact hbound0 sigma hsigma
  · exact hbound1 sigma hsigma
  · exact hbound2 sigma hsigma

end CC20YoshidaTail
end Source
end ConnesWeilRH
