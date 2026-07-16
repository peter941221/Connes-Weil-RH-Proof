/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Source.CC20Concrete.ThreeBranchCommutatorLedger
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Unitary-transported two-support projections on the global logarithmic carrier

This module proves that the existing indicator half-line map is an orthogonal
projection.  It then conjugates that projection by an arbitrary unitary,
constructs the orthogonal projection onto the intersection of the two closed
ranges, and defines the corresponding prolate remainder.

The construction is parametrized by the transport unitary.  This module does
not identify any existing Fourier transform with CCM24's finite-`S` semilocal
transport.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped InnerProductSpace

theorem cc20PositiveHalfLineProjection_inner_symmetry
    (u v : cc20GlobalLogCrossingL2) :
    inner ℂ (cc20PositiveHalfLineProjection u) v =
      inner ℂ u (cc20PositiveHalfLineProjection v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hu := cc20PositiveHalfLineProjection_coeFn u
  have hv := cc20PositiveHalfLineProjection_coeFn v
  apply integral_congr_ae
  filter_upwards [hu, hv] with t hut hvt
  rw [hut, hvt]
  by_cases ht : t ∈ cc20PositiveHalfLine
  · simp only [Set.indicator_of_mem ht]
  · simp [Set.indicator, ht]

theorem cc20PositiveHalfLineProjection_isSelfAdjoint :
    IsSelfAdjoint cc20PositiveHalfLineProjection := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  exact cc20PositiveHalfLineProjection_inner_symmetry

theorem cc20PositiveHalfLineProjection_isIdempotentElem :
    IsIdempotentElem cc20PositiveHalfLineProjection := by
  change cc20PositiveHalfLineProjection.comp
      cc20PositiveHalfLineProjection = cc20PositiveHalfLineProjection
  apply ContinuousLinearMap.ext
  intro u
  exact cc20PositiveHalfLineProjection_idempotent u

theorem cc20PositiveHalfLineProjection_isStarProjection :
    IsStarProjection cc20PositiveHalfLineProjection :=
  ⟨cc20PositiveHalfLineProjection_isIdempotentElem,
    cc20PositiveHalfLineProjection_isSelfAdjoint⟩

/-- The closed range of the concrete positive-half-line projection. -/
noncomputable def cc20PositiveHalfLineClosedRange :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 where
  toSubmodule := cc20PositiveHalfLineProjection.range
  isClosed' :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range
      cc20PositiveHalfLineProjection_isIdempotentElem

theorem cc20PositiveHalfLineProjection_eq_starProjection :
    cc20PositiveHalfLineProjection =
      cc20PositiveHalfLineClosedRange.starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext
    cc20PositiveHalfLineProjection_isStarProjection
    isStarProjection_starProjection
  rw [Submodule.range_starProjection]
  rfl

/-- Conjugate the concrete half-line projection by a unitary coordinate
transport. -/
noncomputable def cc20TransportedHalfLineProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (U : cc20GlobalLogCrossingL2 →L[ℂ]
      cc20GlobalLogCrossingL2).adjoint.comp
    (cc20PositiveHalfLineProjection.comp
      (U : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2))

theorem cc20TransportedHalfLineProjection_apply
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2)
    (u : cc20GlobalLogCrossingL2) :
    cc20TransportedHalfLineProjection U u =
      U.symm (cc20PositiveHalfLineProjection (U u)) := by
  simp [cc20TransportedHalfLineProjection]

theorem cc20TransportedHalfLineProjection_isSelfAdjoint
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    IsSelfAdjoint (cc20TransportedHalfLineProjection U) := by
  exact cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_conj
    (U : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2)

theorem cc20TransportedHalfLineProjection_idempotent
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2)
    (u : cc20GlobalLogCrossingL2) :
    cc20TransportedHalfLineProjection U
        (cc20TransportedHalfLineProjection U u) =
      cc20TransportedHalfLineProjection U u := by
  rw [cc20TransportedHalfLineProjection_apply,
    cc20TransportedHalfLineProjection_apply]
  rw [U.apply_symm_apply]
  rw [cc20PositiveHalfLineProjection_idempotent]

theorem cc20TransportedHalfLineProjection_isIdempotentElem
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    IsIdempotentElem (cc20TransportedHalfLineProjection U) := by
  change (cc20TransportedHalfLineProjection U).comp
      (cc20TransportedHalfLineProjection U) =
        cc20TransportedHalfLineProjection U
  apply ContinuousLinearMap.ext
  intro u
  exact cc20TransportedHalfLineProjection_idempotent U u

theorem cc20TransportedHalfLineProjection_isStarProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    IsStarProjection (cc20TransportedHalfLineProjection U) :=
  ⟨cc20TransportedHalfLineProjection_isIdempotentElem U,
    cc20TransportedHalfLineProjection_isSelfAdjoint U⟩

/-- The closed range of the unitary-transported half-line projection. -/
noncomputable def cc20TransportedHalfLineClosedRange
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 where
  toSubmodule := (cc20TransportedHalfLineProjection U).range
  isClosed' :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (cc20TransportedHalfLineProjection_isIdempotentElem U)

theorem cc20TransportedHalfLineProjection_eq_starProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20TransportedHalfLineProjection U =
      (cc20TransportedHalfLineClosedRange U).starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (cc20TransportedHalfLineProjection_isStarProjection U)
    isStarProjection_starProjection
  rw [Submodule.range_starProjection]
  rfl

/-- The genuine closed intersection of the physical and transported support
subspaces. -/
noncomputable def cc20TransportedSoninClosedSubspace
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 :=
  cc20PositiveHalfLineClosedRange ⊓
    cc20TransportedHalfLineClosedRange U

/-- The orthogonal projection onto the two-support (Sonin) intersection. -/
noncomputable def cc20TransportedSoninProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (cc20TransportedSoninClosedSubspace U).starProjection

theorem cc20TransportedSoninProjection_isStarProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    IsStarProjection (cc20TransportedSoninProjection U) := by
  exact isStarProjection_starProjection

theorem cc20TransportedSoninProjection_isSelfAdjoint
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    IsSelfAdjoint (cc20TransportedSoninProjection U) := by
  exact isSelfAdjoint_starProjection _

theorem cc20TransportedSoninProjection_apply_mem_both
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2)
    (u : cc20GlobalLogCrossingL2) :
    cc20TransportedSoninProjection U u ∈
        cc20PositiveHalfLineClosedRange ∧
      cc20TransportedSoninProjection U u ∈
        cc20TransportedHalfLineClosedRange U := by
  exact (Submodule.starProjection_apply_mem
    (cc20TransportedSoninClosedSubspace U).toSubmodule u)

theorem cc20PositiveHalfLineProjection_comp_sonin
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20PositiveHalfLineProjection.comp
        (cc20TransportedSoninProjection U) =
      cc20TransportedSoninProjection U := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cc20PositiveHalfLineProjection_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr
    (cc20TransportedSoninProjection_apply_mem_both U u).1

theorem cc20TransportedHalfLineProjection_comp_sonin
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    (cc20TransportedHalfLineProjection U).comp
        (cc20TransportedSoninProjection U) =
      cc20TransportedSoninProjection U := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cc20TransportedHalfLineProjection_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr
    (cc20TransportedSoninProjection_apply_mem_both U u).2

theorem cc20TransportedSonin_comp_positiveHalfLineProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    (cc20TransportedSoninProjection U).comp
        cc20PositiveHalfLineProjection =
      cc20TransportedSoninProjection U := by
  have h := congrArg ContinuousLinearMap.adjoint
    (cc20PositiveHalfLineProjection_comp_sonin U)
  simpa [ContinuousLinearMap.adjoint_comp,
    cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq,
    (cc20TransportedSoninProjection_isSelfAdjoint U).adjoint_eq] using h

theorem cc20TransportedSonin_comp_transportedHalfLineProjection
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    (cc20TransportedSoninProjection U).comp
        (cc20TransportedHalfLineProjection U) =
      cc20TransportedSoninProjection U := by
  have h := congrArg ContinuousLinearMap.adjoint
    (cc20TransportedHalfLineProjection_comp_sonin U)
  simpa [ContinuousLinearMap.adjoint_comp,
    (cc20TransportedHalfLineProjection_isSelfAdjoint U).adjoint_eq,
    (cc20TransportedSoninProjection_isSelfAdjoint U).adjoint_eq] using h

/-- The prolate remainder determined by the two support projections and their
intersection projection. -/
noncomputable def cc20TransportedProlateRemainder
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20PositiveHalfLineProjection.comp
      ((cc20TransportedHalfLineProjection U).comp
        cc20PositiveHalfLineProjection) -
    cc20TransportedSoninProjection U

theorem cc20TransportedProlateRemainder_isSelfAdjoint
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    IsSelfAdjoint (cc20TransportedProlateRemainder U) := by
  unfold cc20TransportedProlateRemainder
  have hcompressed :=
    (cc20TransportedHalfLineProjection_isSelfAdjoint U).conj_adjoint
      cc20PositiveHalfLineProjection
  rw [cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq] at hcompressed
  exact hcompressed.sub (cc20TransportedSoninProjection_isSelfAdjoint U)

theorem cc20TransportedProlateRemainder_eq_complement_conjugation
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20TransportedProlateRemainder U =
      (cc20PositiveHalfLineProjection -
          cc20TransportedSoninProjection U).comp
        ((cc20TransportedHalfLineProjection U).comp
          (cc20PositiveHalfLineProjection -
            cc20TransportedSoninProjection U)) := by
  unfold cc20TransportedProlateRemainder
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub]
  rw [show cc20TransportedHalfLineProjection U
        (cc20TransportedSoninProjection U u) =
      cc20TransportedSoninProjection U u by
        exact DFunLike.congr_fun
          (cc20TransportedHalfLineProjection_comp_sonin U) u]
  rw [show cc20PositiveHalfLineProjection
        (cc20TransportedSoninProjection U u) =
      cc20TransportedSoninProjection U u by
        exact DFunLike.congr_fun
          (cc20PositiveHalfLineProjection_comp_sonin U) u]
  rw [show cc20TransportedSoninProjection U
        (cc20TransportedHalfLineProjection U
          (cc20PositiveHalfLineProjection u)) =
      cc20TransportedSoninProjection U u by
        calc
          _ = cc20TransportedSoninProjection U
              (cc20PositiveHalfLineProjection u) := by
                exact DFunLike.congr_fun
                  (cc20TransportedSonin_comp_transportedHalfLineProjection U)
                  (cc20PositiveHalfLineProjection u)
          _ = cc20TransportedSoninProjection U u := by
                exact DFunLike.congr_fun
                  (cc20TransportedSonin_comp_positiveHalfLineProjection U) u]
  rw [show cc20TransportedSoninProjection U
        (cc20TransportedSoninProjection U u) =
      cc20TransportedSoninProjection U u by
        exact DFunLike.congr_fun
          (cc20TransportedSoninProjection_isStarProjection U).isIdempotentElem u]
  abel

theorem cc20TransportedProlateRemainder_isPositive
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    (cc20TransportedProlateRemainder U).IsPositive := by
  rw [cc20TransportedProlateRemainder_eq_complement_conjugation]
  let S := cc20PositiveHalfLineProjection -
    cc20TransportedSoninProjection U
  have hQ : (cc20TransportedHalfLineProjection U).IsPositive :=
    ContinuousLinearMap.IsPositive.of_isStarProjection
      (cc20TransportedHalfLineProjection_isStarProjection U)
  have hS : IsSelfAdjoint S :=
    cc20PositiveHalfLineProjection_isSelfAdjoint.sub
      (cc20TransportedSoninProjection_isSelfAdjoint U)
  have hconj := hQ.adjoint_conj S
  rw [hS.adjoint_eq] at hconj
  exact hconj

theorem cc20TransportedSonin_eq_supports_sub_prolate
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2) :
    cc20TransportedSoninProjection U =
      cc20PositiveHalfLineProjection.comp
          ((cc20TransportedHalfLineProjection U).comp
            cc20PositiveHalfLineProjection) -
        cc20TransportedProlateRemainder U := by
  unfold cc20TransportedProlateRemainder
  abel

theorem cc20TransportedSonin_commutator_eq_threeBranch
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2)
    (W : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2) :
    cc20Commutator (cc20TransportedSoninProjection U) W =
      cc20ThreeBranchCommutator
        cc20PositiveHalfLineProjection
        (cc20TransportedHalfLineProjection U)
        (cc20TransportedProlateRemainder U) W := by
  exact cc20Commutator_eq_threeBranch_of_eq _ _ _ _ _
    (cc20TransportedSonin_eq_supports_sub_prolate U)

theorem cc20TransportedSonin_residueResponse_eq_threeBranch
    (U : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2)
    (W : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2)
    (x y : cc20GlobalLogCrossingL2) :
    cc20CommutatorResidueResponse
        (cc20TransportedSoninProjection U) W x y =
      cc20ThreeBranchResidueResponse
        cc20PositiveHalfLineProjection
        (cc20TransportedHalfLineProjection U)
        (cc20TransportedProlateRemainder U) W x y := by
  exact cc20CommutatorResidueResponse_eq_threeBranch_of_eq _ _ _ _ _
    (cc20TransportedSonin_eq_supports_sub_prolate U) x y

end CC20Concrete
end Source
end ConnesWeilRH
