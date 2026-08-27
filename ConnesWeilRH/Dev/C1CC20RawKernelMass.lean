/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.EndpointKernelFormula
import ConnesWeilRH.Dev.C1CC20LpOperatorNorm

/-!
# Windowed raw CC20 endpoint kernel: measurability, pointwise bounds, L2 mass

This leaf bridges the paper's raw endpoint kernel (`CC20EndpointSpectralData`,
equation (104) of arXiv:2006.13771) into the `C1CC20LpOperator` /
`C1CC20LpOperatorNorm` boundedness foundation.  The kernel depends on its two
arguments only through the displacement `p.2 - p.1`; restricting both
coordinates to the window `[-a, a]` therefore bounds the displacement by
`2 * a`, and any uniform bound `B` on the displacement profile makes the
windowed kernel an `L2` kernel whose squared mass is dominated by
`(B * (2 * a)) ^ 2`, which then propagates through
`applyKernel_l2_sq_bound` into an explicit operator bound for the applied
function.

Structure of the leaf, bottom-up:

* definition and membership lemmas for `endpointKernelOnSquare`;
* continuity / measurability from the standing continuous-profile premise;
* compactness packaging `exists_norm_bound_on_window`;
* pointwise squared-enorm domination `enorm_sq_endpointKernelOnSquare_le`;
* unconditional diagonal fact `endpointKernelOnSquare_diagonal_zero`
  (the window is symmetric, so every diagonal point is either fully in or
  fully out);
* the `MemLp 2` certification `memLp_endpointKernelOnSquare_of_mass_lt_top`,
  consuming a caller-supplied total-mass bound (the same extended-real ladder
  used by `C1CC20LpOperatorNorm`);
* the operator-level specialization `applyKernel_l2_sq_le_of_kernelMassBound`.

No RH sign or coverage claim is made here, and no convergence property of the
formal `qEpsilon` series is assumed: boundedness on the compact window is an
explicit caller premise, mirroring the way numerical certificates enter
`C1CC20OperatorGap`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20RawKernelMass

open CC20Concrete
open MeasureTheory

/-- The symmetric log-coordinate window `[-a, a]`. -/
def cc20Window (a : ℝ) : Set ℝ := Set.Icc (-a) a

/-- The square window `[-a, a] × [-a, a]` in the two kernel coordinates. -/
def cc20WindowPair (a : ℝ) : Set (ℝ × ℝ) := cc20Window a ×ˢ cc20Window a

/-- The paper's raw endpoint kernel, restricted to the square window and
complex-cast for the `applyKernel` foundation. -/
noncomputable def endpointKernelOnSquare
    (data : CC20EndpointSpectralData) (a : ℝ) : ℝ × ℝ → ℂ :=
  (cc20WindowPair a).indicator data.endpointWindowKernelComplex

theorem endpointKernelOnSquare_of_mem
    (data : CC20EndpointSpectralData) (a : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ cc20WindowPair a) :
    endpointKernelOnSquare data a p = data.endpointWindowKernelComplex p := by
  simp [endpointKernelOnSquare, hp]

theorem endpointKernelOnSquare_of_not_mem
    (data : CC20EndpointSpectralData) (a : ℝ) {p : ℝ × ℝ}
    (hp : p ∉ cc20WindowPair a) :
    endpointKernelOnSquare data a p = 0 := by
  simp [endpointKernelOnSquare, hp]

theorem measurableSet_cc20Window (a : ℝ) : MeasurableSet (cc20Window a) :=
  measurableSet_Icc

theorem measurableSet_cc20WindowPair (a : ℝ) :
    MeasurableSet (cc20WindowPair a) :=
  (measurableSet_cc20Window a).prod (measurableSet_cc20Window a)

/-- Continuity of the complex-cast raw kernel follows from continuity of the
real displacement profile, the standing caller premise. -/
theorem continuous_endpointWindowKernelComplex
    (data : CC20EndpointSpectralData)
    (hcont : Continuous data.endpointWindowKernel) :
    Continuous data.endpointWindowKernelComplex :=
  Complex.continuous_ofReal.comp hcont

theorem measurable_endpointKernelOnSquare
    (data : CC20EndpointSpectralData) (a : ℝ)
    (hcont : Continuous data.endpointWindowKernel) :
    Measurable (endpointKernelOnSquare data a) :=
  (continuous_endpointWindowKernelComplex data hcont).measurable.indicator
    (measurableSet_cc20WindowPair a)

/-- Compactness delivers a uniform nonnegative bound `B` on the raw kernel
over the square window. -/
theorem exists_norm_bound_on_window
    (data : CC20EndpointSpectralData) (a : ℝ)
    (hcont : Continuous data.endpointWindowKernel) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ p ∈ cc20WindowPair a,
        ‖data.endpointWindowKernelComplex p‖ ≤ B := by
  have hcomp : IsCompact (cc20WindowPair a) :=
    isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p => ‖data.endpointWindowKernelComplex p‖)
      (cc20WindowPair a) :=
    (continuous_endpointWindowKernelComplex data hcont).norm.continuousOn
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp
  refine le_trans ?_ (le_max_left _ _)
  have hrw : ‖data.endpointWindowKernelComplex p‖
      = ‖(‖data.endpointWindowKernelComplex p‖ : ℝ)‖ :=
    (Real.norm_of_nonneg (norm_nonneg _)).symm
  rw [hrw]
  exact hB p hp

/-- Squared extended norm of the windowed kernel at a point, dominated by the
uniform window bound: inside the square the raw value obeys `B`; outside it
the indicator vanishes. -/
theorem enorm_sq_endpointKernelOnSquare_le
    (data : CC20EndpointSpectralData) (a : ℝ) (B : ℝ)
    (hbound : ∀ p ∈ cc20WindowPair a,
        ‖data.endpointWindowKernelComplex p‖ ≤ B) (p : ℝ × ℝ) :
    ‖endpointKernelOnSquare data a p‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (B ^ 2) := by
  by_cases hp : p ∈ cc20WindowPair a
  · have hnn : (0 : ℝ) ≤ ‖data.endpointWindowKernelComplex p‖ ^ 2 :=
      sq_nonneg _
    calc
      ‖endpointKernelOnSquare data a p‖ₑ ^ (2 : ℝ)
          = ENNReal.ofReal
              (‖data.endpointWindowKernelComplex p‖ ^ 2) := by
            rw [endpointKernelOnSquare_of_mem data a hp]
            simp
      _ ≤ ENNReal.ofReal (B ^ 2) :=
          ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (norm_nonneg _) (hbound p hp) 2)
  · calc
      ‖endpointKernelOnSquare data a p‖ₑ ^ (2 : ℝ)
          = 0 := by
            rw [endpointKernelOnSquare_of_not_mem data a hp]
            simp
      _ ≤ ENNReal.ofReal (B ^ 2) := by
            positivity

/-- Unconditional diagonal fact: because the window is symmetric, each
diagonal point `(x, x)` lies either entirely inside the square window or
entirely outside it, so the windowed raw kernel vanishes identically on the
diagonal.  This transports CC20 Remark 6 through the window restriction. -/
theorem endpointKernelOnSquare_diagonal_zero
    (data : CC20EndpointSpectralData) (a : ℝ) (x : ℝ) :
    endpointKernelOnSquare data a (x, x) = 0 := by
  by_cases hx : x ∈ cc20Window a
  · rw [endpointKernelOnSquare_of_mem data a (by exact ⟨hx, hx⟩)]
    exact data.endpointWindowKernelComplex_diagonal x
  · exact endpointKernelOnSquare_of_not_mem data a (fun hm => hx hm.1)

/-!
### Operator-level consequences

The remaining statements consume one caller-supplied total-mass bound,
expressed directly in the extended-real units of `applyKernel_l2_sq_bound`.
The Measurability side is unconditional (proved above); only the mass side is
premise-carried.
-/

/-- `MemLp 2` certification for the windowed raw kernel from a total-mass
bound: strong measurability is unconditional, so only
`∫⁻ ‖kernel‖ₑ² < ⊤` is consumed. -/
theorem memLp_endpointKernelOnSquare_of_mass_lt_top
    (data : CC20EndpointSpectralData) (a : ℝ)
    (hcont : Continuous data.endpointWindowKernel)
    (hmass : (∫⁻ p : ℝ × ℝ,
        ‖endpointKernelOnSquare data a p‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp (endpointKernelOnSquare data a)
      (ENNReal.ofReal 2) volume := by
  refine ⟨(measurable_endpointKernelOnSquare data a hcont).aestronglyMeasurable, ?_⟩
  have hpz : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hpt : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  simpa using hmass

/-- Integrated (operator-norm) bound specialized to the windowed raw kernel,
under the caller-supplied total-kernel-mass finiteness premise: the applied
output mass is dominated by the kernel mass times the input mass. -/
theorem applyKernel_l2_sq_le_of_kernelMassTopLt
    (data : CC20EndpointSpectralData) (a : ℝ)
    (hcont : Continuous data.endpointWindowKernel)
    (hmass : (∫⁻ p : ℝ × ℝ,
        ‖endpointKernelOnSquare data a p‖ₑ ^ (2 : ℝ)) < ⊤)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal 2)) :
    (∫⁻ x, ‖C1CC20LpOperator.applyKernel (endpointKernelOnSquare data a) f x‖ₑ ^
        (2 : ℝ)) ≤
      (∫⁻ p : ℝ × ℝ,
        ‖endpointKernelOnSquare data a p‖ₑ ^ (2 : ℝ)) *
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)) := by
  have hk : MemLp (endpointKernelOnSquare data a) (ENNReal.ofReal 2) volume :=
    memLp_endpointKernelOnSquare_of_mass_lt_top data a hcont hmass
  exact C1CC20LpOperatorNorm.applyKernel_l2_sq_bound hf hk

end C1CC20RawKernelMass
end Source
end ConnesWeilRH
