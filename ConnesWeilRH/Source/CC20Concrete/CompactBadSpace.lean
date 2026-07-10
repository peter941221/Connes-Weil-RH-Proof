/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite conditioning space for a compact remainder

A compact operator sends the unit ball into a totally bounded set. A finite
`c`-net of that image spans a finite-dimensional subspace. On its orthogonal
complement the real quadratic form of the operator is bounded by `c`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace CompactBadSpace

open Metric
open scoped InnerProductSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A compact remainder has only finitely many conditioning directions above
any positive quadratic threshold. -/
theorem exists_finiteDimensional_controlSpace
    (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        ∀ x : H, x ∈ controlSpaceᗮ →
          (⟪x, operator x⟫_ℂ).re ≤ threshold * ‖x‖ ^ 2 := by
  obtain ⟨compactRange, hcompactRange, himage⟩ :=
    hcompact.image_closedBall_subset_compact 1
  obtain ⟨net, _hnet_subset, hnet_finite, hnet_cover⟩ :=
    hcompactRange.finite_cover_balls hthreshold
  let controlSpace : Submodule ℂ H := Submodule.span ℂ net
  have hfinite : FiniteDimensional ℂ controlSpace :=
    FiniteDimensional.span_of_finite ℂ hnet_finite
  refine ⟨controlSpace, hfinite, ?_⟩
  intro x hx
  by_cases hxzero : x = 0
  · simp [hxzero]
  let scale : ℝ := ‖x‖
  have hscale : scale ≠ 0 := by
    simpa [scale] using norm_ne_zero_iff.mpr hxzero
  let unit : H := (scale⁻¹ : ℂ) • x
  have hunit_norm : ‖unit‖ = 1 := by
    simp [unit, norm_smul, scale, hscale]
  have hunit_ball : unit ∈ closedBall (0 : H) 1 := by
    simp [mem_closedBall, hunit_norm]
  have hoperator_mem : operator unit ∈ compactRange :=
    himage ⟨unit, hunit_ball, rfl⟩
  have hcovered := hnet_cover hoperator_mem
  simp only [Set.mem_iUnion] at hcovered
  obtain ⟨center, hcenter_mem, hcenter_close⟩ := hcovered
  have hcenter_control : center ∈ controlSpace :=
    Submodule.subset_span hcenter_mem
  have hunit_orthogonal : unit ∈ controlSpaceᗮ := by
    exact (controlSpaceᗮ).smul_mem (scale⁻¹ : ℂ) hx
  have hinner_center : ⟪unit, center⟫_ℂ = 0 :=
    controlSpace.inner_left_of_mem_orthogonal hcenter_control hunit_orthogonal
  have hunit_bound : (⟪unit, operator unit⟫_ℂ).re ≤ threshold := by
    calc
      (⟪unit, operator unit⟫_ℂ).re =
          (⟪unit, operator unit - center⟫_ℂ).re := by
        rw [inner_sub_right, hinner_center, sub_zero]
      _ ≤ ‖⟪unit, operator unit - center⟫_ℂ‖ := by
        simpa only [RCLike.re_eq_complex_re] using
          RCLike.re_le_norm ⟪unit, operator unit - center⟫_ℂ
      _ ≤ ‖unit‖ * ‖operator unit - center‖ := norm_inner_le_norm _ _
      _ = ‖operator unit - center‖ := by rw [hunit_norm, one_mul]
      _ = dist (operator unit) center := by rw [dist_eq_norm]
      _ ≤ threshold := hcenter_close.le
  have hx_eq : x = (scale : ℂ) • unit := by
    simp [unit, smul_smul, hscale]
  have hinner_scale :
      (⟪x, operator x⟫_ℂ).re =
        scale ^ 2 * (⟪unit, operator unit⟫_ℂ).re := by
    rw [hx_eq, map_smul, inner_smul_left, inner_smul_right]
    simp [Complex.mul_re]
    ring
  rw [hinner_scale]
  simpa [scale, mul_comm] using
    mul_le_mul_of_nonneg_left hunit_bound (sq_nonneg scale)

/-- On the orthogonal complement of the finite control space, the compact
perturbation of `-threshold * Id` has nonpositive real quadratic form. -/
theorem exists_finiteDimensional_remainder_nonpositive
    (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        ∀ x : H, x ∈ controlSpaceᗮ →
          (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  obtain ⟨controlSpace, hfinite, hbound⟩ :=
    exists_finiteDimensional_controlSpace operator hcompact hthreshold
  refine ⟨controlSpace, hfinite, ?_⟩
  intro x hx
  have h := hbound x hx
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  linarith

end CompactBadSpace
end CC20Concrete
end Source
end ConnesWeilRH
