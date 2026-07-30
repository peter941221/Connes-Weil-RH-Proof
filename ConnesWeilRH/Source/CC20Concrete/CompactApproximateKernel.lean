/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences

/-!
# Compact outputs of injective approximate kernels

An injective bounded operator need not be bounded below.  Nevertheless, a
bounded sequence on which that operator tends to zero converges weakly to
zero.  Every compact operator therefore sends the same sequence to zero in
norm.

This is a qualitative compactness-uniqueness statement.  It does not provide
a Douglas bound `norm (K x) <= C * norm (D x)`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace CompactApproximateKernel

open Filter Function Set Topology
open scoped InnerProductSpace

variable {H G J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The adjoint of an injective Hilbert-space operator has dense range. -/
theorem denseRange_adjoint_of_injective
    (D : H →L[ℂ] G) (hD : Function.Injective D) :
    DenseRange D.adjoint := by
  change Dense (D.adjoint.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← D.orthogonal_ker,
    LinearMap.ker_eq_bot.mpr hD, Submodule.bot_orthogonal_eq_top]

/-- A bounded approximate-kernel sequence for an injective operator converges
to zero against every fixed Hilbert-space test vector. -/
theorem inner_tendsto_zero_of_injective_approximate_kernel
    (D : H →L[ℂ] G) (hD : Function.Injective D)
    (x : ℕ → H) (hbounded : Bornology.IsBounded (Set.range x))
    (hzero : Tendsto (fun n ↦ D (x n)) atTop (nhds 0))
    (v : H) :
    Tendsto (fun n ↦ inner ℂ v (x n)) atTop (nhds 0) := by
  obtain ⟨R, hRpos, hR⟩ := hbounded.exists_pos_norm_le
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hdense : DenseRange D.adjoint :=
    denseRange_adjoint_of_injective D hD
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hdense v
    (ε / (2 * R)) (by positivity)
  have hsmall := (NormedAddGroup.tendsto_nhds_zero.mp hzero)
    (ε / (2 * (‖y‖ + 1))) (by positivity)
  filter_upwards [hsmall] with n hn
  have hxnorm : ‖x n‖ ≤ R := hR (x n) ⟨n, rfl⟩
  have hyNorm : ‖v - D.adjoint y‖ < ε / (2 * R) := by
    simpa only [dist_eq_norm] using hy
  have hfirst : ‖inner ℂ (v - D.adjoint y) (x n)‖ < ε / 2 := by
    calc
      ‖inner ℂ (v - D.adjoint y) (x n)‖ ≤
          ‖v - D.adjoint y‖ * ‖x n‖ := norm_inner_le_norm _ _
      _ ≤ ‖v - D.adjoint y‖ * R :=
        mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _)
      _ < (ε / (2 * R)) * R :=
        mul_lt_mul_of_pos_right hyNorm hRpos
      _ = ε / 2 := by field_simp [ne_of_gt hRpos]
  have hsecond : ‖inner ℂ (D.adjoint y) (x n)‖ < ε / 2 := by
    calc
      ‖inner ℂ (D.adjoint y) (x n)‖ = ‖inner ℂ y (D (x n))‖ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ ≤ ‖y‖ * ‖D (x n)‖ := norm_inner_le_norm _ _
      _ ≤ (‖y‖ + 1) * ‖D (x n)‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖y‖ + 1) * (ε / (2 * (‖y‖ + 1))) := by
        exact mul_lt_mul_of_pos_left hn (by positivity)
      _ = ε / 2 := by
        field_simp [show ‖y‖ + 1 ≠ 0 by positivity]
  calc
    ‖inner ℂ v (x n)‖ =
        ‖inner ℂ (v - D.adjoint y) (x n) +
          inner ℂ (D.adjoint y) (x n)‖ := by
      congr 1
      rw [inner_sub_left]
      ring
    _ ≤ ‖inner ℂ (v - D.adjoint y) (x n)‖ +
        ‖inner ℂ (D.adjoint y) (x n)‖ := norm_add_le _ _
    _ < ε := by linarith

/-- A compact operator sends every bounded approximate-kernel sequence of an
injective operator to zero in norm. -/
theorem compact_output_tendsto_zero_of_injective_approximate_kernel
    (D : H →L[ℂ] G) (K : H →L[ℂ] J)
    (hD : Function.Injective D) (hK : IsCompactOperator K)
    (x : ℕ → H) (hbounded : Bornology.IsBounded (Set.range x))
    (hzero : Tendsto (fun n ↦ D (x n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ K (x n)) atTop (nhds 0) := by
  obtain ⟨C, hCcompact, hKC⟩ :=
    hK.image_subset_compact_of_bounded hbounded
  apply hCcompact.tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards with n
    exact hKC ⟨x n, ⟨n, rfl⟩, rfl⟩
  · intro y _ hy
    obtain ⟨φ, hφmono, hφ⟩ := hy.tendsto_subseq
    apply (inner_self_eq_zero (𝕜 := ℂ) (x := y)).mp
    have htest :=
      inner_tendsto_zero_of_injective_approximate_kernel
        D hD x hbounded hzero (K.adjoint y)
    have htestSub := htest.comp hφmono.tendsto_atTop
    have htoZero :
        Tendsto (fun n ↦ inner ℂ y (K (x (φ n)))) atTop (nhds 0) := by
      simpa only [Function.comp_apply,
        ContinuousLinearMap.adjoint_inner_left] using htestSub
    have htoLimit :
        Tendsto (fun n ↦ inner ℂ y (K (x (φ n)))) atTop
          (nhds (inner ℂ y y)) := by
      simpa only [Function.comp_apply] using
        (tendsto_const_nhds.inner hφ)
    exact (tendsto_nhds_unique htoLimit htoZero)

end CompactApproximateKernel
end CC20Concrete
end Source
end ConnesWeilRH
