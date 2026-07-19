/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Operator-level Douglas factorization

The Gate 3U consumer needs a factor through the genuine Julia range column.
This file supplies the functional-analytic construction behind that word:
an operator `A` factors through `B` when the full source-side estimate

```text
        ||A x|| <= C ||B x||

for every x
```

holds.  A bound checked only on a Hilbert basis is intentionally insufficient.
The factor is obtained by defining `A (B x)` on `range B`, extending it to
the closure of that range, and then composing with the orthogonal projection
onto the closure.  The construction is therefore valid even when `range B`
is not closed, and its norm is at most `C`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSDouglasFactor

open scoped Topology

noncomputable def rangeClosureInclusion
    {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : H →L[ℂ] E) :
    LinearMap.range B.toLinearMap →ₗ[ℂ]
      (LinearMap.range B.toLinearMap).topologicalClosure :=
  ((LinearMap.range B.toLinearMap).subtypeL.codRestrict
      (LinearMap.range B.toLinearMap).topologicalClosure
      (fun x =>
        (LinearMap.range B.toLinearMap).le_topologicalClosure x.property)).toLinearMap

theorem denseRange_rangeClosureInclusion
    {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : H →L[ℂ] E) :
    DenseRange (rangeClosureInclusion B) := by
  let R : Submodule ℂ E := LinearMap.range B.toLinearMap
  have hsubset : (R : Set E) ⊆ (R.topologicalClosure : Set E) := by
    intro x hx
    exact R.le_topologicalClosure hx
  have hclosure : (R.topologicalClosure : Set E) ⊆ closure (R : Set E) := by
    intro x hx
    simpa only [Submodule.topologicalClosure_coe] using hx
  have hinclusion : DenseRange (Set.inclusion hsubset) :=
    (denseRange_inclusion_iff hsubset).2 hclosure
  simpa only [rangeClosureInclusion, R] using hinclusion

/-!
The factorization theorem is stated with the exact norm domination needed by
Douglas' lemma.  It does not use a basis, a diagonal estimate, or a finite
dimensional approximation.
-/
theorem exists_factor_of_norm_le
    {H E G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (A : H →L[ℂ] G) (B : H →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ x : H, ‖A x‖ ≤ C * ‖B x‖) :
    ∃ F : E →L[ℂ] G, ‖F‖ ≤ C ∧ F ∘L B = A := by
  let R : Submodule ℂ E := LinearMap.range B.toLinearMap
  let Rcl : Submodule ℂ E := R.topologicalClosure
  let e : R →ₗ[ℂ] Rcl := rangeClosureInclusion B
  let f : R →ₗ[ℂ] G :=
    A.toLinearMap.compLeftInverse B.toLinearMap
  have he : DenseRange e := by
    simpa only [e, R] using denseRange_rangeClosureInclusion B
  have hf : ∀ y : R, ‖f y‖ ≤ C * ‖e y‖ := by
    rintro ⟨y, hy⟩
    let x : H := Classical.choose hy
    have hx : B x = y := Classical.choose_spec hy
    have happly := LinearMap.compLeftInverse_apply_of_bdd
      A.toLinearMap B.toLinearMap ⟨C, hdom⟩ x y hx
    have hf_apply : f ⟨y, ⟨x, hx⟩⟩ = A x := by
      simpa only [f] using happly
    calc
      ‖f ⟨y, hy⟩‖ = ‖A x‖ := by
        simpa only using congrArg norm hf_apply
      _ ≤ C * ‖B x‖ := hdom x
      _ = C * ‖e ⟨y, hy⟩‖ := by
        congr 1
        change ‖B x‖ = ‖(y : E)‖
        rw [hx]
  let extension : Rcl →L[ℂ] G := f.extendOfNorm e
  have hextension : ‖extension‖ ≤ C := by
    change ‖f.extendOfNorm e‖ ≤ C
    exact LinearMap.opNorm_extendOfNorm_le he hC hf
  let projection : E →L[ℂ] Rcl := Rcl.orthogonalProjection
  let factor : E →L[ℂ] G := extension ∘L projection
  have hprojection : ‖projection‖ ≤ 1 := by
    exact Rcl.orthogonalProjection_norm_le
  have hfactor : ‖factor‖ ≤ C := by
    calc
      ‖factor‖ ≤ ‖extension‖ * ‖projection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by
        exact mul_le_mul hextension hprojection
          (norm_nonneg _) hC
      _ = C := by ring
  refine ⟨factor, hfactor, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  let bx : R := ⟨B x, LinearMap.mem_range_self B.toLinearMap x⟩
  have hmem : B x ∈ Rcl := by
    exact R.le_topologicalClosure (LinearMap.mem_range_self B.toLinearMap x)
  have hprojection_apply : projection (B x) = e bx := by
    apply Subtype.ext
    change Rcl.orthogonalProjectionFn (B x) = B x
    simpa only [Submodule.orthogonalProjectionFn_eq,
      Submodule.coe_orthogonalProjection_apply] using
      (Rcl.starProjection_eq_self_iff.mpr hmem)
  have hextension_apply : extension (e bx) = f bx := by
    simpa only [extension] using
      (LinearMap.extendOfNorm_eq he ⟨C, hf⟩ bx)
  have hf_apply : f bx = A x := by
    have happly := LinearMap.compLeftInverse_apply_of_bdd
      A.toLinearMap B.toLinearMap ⟨C, hdom⟩ x (B x) rfl
    simpa only [f, bx] using happly
  calc
    factor (B x) = extension (projection (B x)) := rfl
    _ = extension (e bx) := by rw [hprojection_apply]
    _ = f bx := hextension_apply
    _ = A x := hf_apply

/-!
The positive-operator form of Douglas domination is usually discharged after
squaring norms.  This adapter keeps that source-facing form explicit while
reducing it to the same closed-range construction above.  The square estimate
is still required on every source vector; it is not a basis estimate.
-/
theorem exists_factor_of_norm_sq_le
    {H E G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (A : H →L[ℂ] G) (B : H →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ x : H, ‖A x‖ ^ 2 ≤ C ^ 2 * ‖B x‖ ^ 2) :
    ∃ F : E →L[ℂ] G, ‖F‖ ≤ C ∧ F ∘L B = A := by
  apply exists_factor_of_norm_le A B C hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  simpa only [mul_pow] using hdom x

end CCM24FiniteSDouglasFactor
end CCM25Concrete
end Source
end ConnesWeilRH
