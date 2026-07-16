import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Invertible transport of Sonin intersections

This module separates closed-subspace transport from orthogonal-projection
positivity. A bounded invertible transport is not used as a non-unitary
conjugation of an orthogonal projection.
-/

namespace ConnesWeilRH
namespace CC20Concrete

section Transport

variable {𝕜 H H' : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-- The closed-submodule image under a bounded invertible linear transport. -/
def transportedClosedSubmodule (T : H ≃L[𝕜] H')
    (P : ClosedSubmodule 𝕜 H) : ClosedSubmodule 𝕜 H' :=
  ClosedSubmodule.mapEquiv T P

@[simp]
theorem transportedClosedSubmodule_inf (T : H ≃L[𝕜] H')
    (P Q : ClosedSubmodule 𝕜 H) :
    transportedClosedSubmodule T (P ⊓ Q) =
      transportedClosedSubmodule T P ⊓ transportedClosedSubmodule T Q := by
  exact ClosedSubmodule.mapEquiv_inf_eq T

end Transport

section PositiveIntersection

variable {𝕜 E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E]

variable (P Q : Submodule 𝕜 E)
variable [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
variable [(P ⊓ Q).HasOrthogonalProjection]

local notation "p" => P.starProjection
local notation "q" => Q.starProjection
local notation "r" => Submodule.starProjection (P ⊓ Q)

omit [CompleteSpace E] [Q.HasOrthogonalProjection] in
lemma left_starProjection_absorbs_intersection : p ∘L r = r := by
  ext x
  apply P.starProjection_eq_self_iff.mpr
  exact (Submodule.mem_inf.mp ((P ⊓ Q).starProjection_apply_mem x)).1

omit [CompleteSpace E] [P.HasOrthogonalProjection] in
lemma right_starProjection_absorbs_intersection : q ∘L r = r := by
  ext x
  apply Q.starProjection_eq_self_iff.mpr
  exact (Submodule.mem_inf.mp ((P ⊓ Q).starProjection_apply_mem x)).2

omit [Q.HasOrthogonalProjection] in
lemma intersection_absorbs_left_starProjection : r ∘L p = r := by
  have h := congrArg
    (fun A : E →L[𝕜] E => ContinuousLinearMap.adjoint A)
    (left_starProjection_absorbs_intersection P Q)
  have hp : ContinuousLinearMap.adjoint p = p :=
    (isSelfAdjoint_starProjection P).adjoint_eq
  have hr : ContinuousLinearMap.adjoint r = r :=
    (isSelfAdjoint_starProjection (P ⊓ Q)).adjoint_eq
  simpa only [ContinuousLinearMap.adjoint_comp, hp, hr] using h

omit [P.HasOrthogonalProjection] in
lemma intersection_absorbs_right_starProjection : r ∘L q = r := by
  have h := congrArg
    (fun A : E →L[𝕜] E => ContinuousLinearMap.adjoint A)
    (right_starProjection_absorbs_intersection P Q)
  have hq : ContinuousLinearMap.adjoint q = q :=
    (isSelfAdjoint_starProjection Q).adjoint_eq
  have hr : ContinuousLinearMap.adjoint r = r :=
    (isSelfAdjoint_starProjection (P ⊓ Q)).adjoint_eq
  simpa only [ContinuousLinearMap.adjoint_comp, hq, hr] using h

/-- The exact positive-factor identity for two actual target subspaces. -/
theorem compressed_projection_sub_intersection_eq_factor :
    p ∘L q ∘L p - r = (p - r) ∘L q ∘L (p - r) := by
  have hpr : p * r = r := by
    simpa only [ContinuousLinearMap.mul_def] using
      left_starProjection_absorbs_intersection P Q
  have hqr : q * r = r := by
    simpa only [ContinuousLinearMap.mul_def] using
      right_starProjection_absorbs_intersection P Q
  have hrp : r * p = r := by
    simpa only [ContinuousLinearMap.mul_def] using
      intersection_absorbs_left_starProjection P Q
  have hrq : r * q = r := by
    simpa only [ContinuousLinearMap.mul_def] using
      intersection_absorbs_right_starProjection P Q
  have hrr : r * r = r :=
    (P ⊓ Q).isIdempotentElem_starProjection
  have hpqr : p * q * r = r := by
    rw [mul_assoc, hqr, hpr]
  have hrqp : r * q * p = r := by
    rw [hrq, hrp]
  have hrqr : r * q * r = r := by
    rw [hrq, hrr]
  have hmul : p * q * p - r = (p - r) * q * (p - r) := by
    symm
    calc
      (p - r) * q * (p - r) =
          p * q * p - p * q * r - r * q * p + r * q * r := by
        noncomm_ring
      _ = p * q * p - r := by
        rw [hpqr, hrqp, hrqr]
        abel
  simpa only [ContinuousLinearMap.mul_def] using hmul

/-- The corrected compression is positive on the actual target carrier. -/
theorem compressed_projection_sub_intersection_isPositive :
    (p ∘L q ∘L p - r).IsPositive := by
  rw [compressed_projection_sub_intersection_eq_factor P Q]
  have hq : ContinuousLinearMap.IsPositive Q.starProjection :=
    ContinuousLinearMap.IsPositive.of_isStarProjection
      isStarProjection_starProjection
  have hpos := hq.conj_adjoint (p - r)
  have hp : ContinuousLinearMap.adjoint p = p :=
    (isSelfAdjoint_starProjection P).adjoint_eq
  have hr : ContinuousLinearMap.adjoint r = r :=
    (isSelfAdjoint_starProjection (P ⊓ Q)).adjoint_eq
  have hsub : ContinuousLinearMap.adjoint (p - r) = p - r := by
    rw [map_sub, hp, hr]
  simpa only [hsub] using hpos

end PositiveIntersection

end CC20Concrete
end ConnesWeilRH
