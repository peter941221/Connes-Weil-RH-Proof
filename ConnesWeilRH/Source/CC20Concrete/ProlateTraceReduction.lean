/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogSoninProjection
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# Prolate trace reduction for two support projections

This file isolates the exact operator-theoretic bottom behind CC20's prolate
trace theorem.  For the two support projections `P`, `Q`, their intersection
projection `R`, and `B = P - R`, it constructs

`A = Q B`, `K = A† A`, and `D = (I - B) A`.

The canonical defect is `D† D = K - K† K`.  Consequently a strict angle gap
`‖A‖ < 1` and Hilbert--Schmidt summability of `D` imply positive trace
legality of `K`.  This module proves the reduction only; it does not claim the
source-specific angle gap or the Hilbert--Schmidt estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ProlateTraceReduction

open scoped InnerProductSpace
open PositiveTrace

local notation "H" => cc20GlobalLogCrossingL2

noncomputable def supportComplementProjection
    (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  cc20PositiveHalfLineProjection - cc20TransportedSoninProjection U

noncomputable def prolateFactor
    (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  cc20TransportedHalfLineProjection U ∘L supportComplementProjection U

noncomputable def prolateDefectFactor
    (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (ContinuousLinearMap.id ℂ H - supportComplementProjection U) ∘L
    prolateFactor U

theorem supportComplementProjection_isSelfAdjoint
    (U : H ≃ₗᵢ[ℂ] H) :
    IsSelfAdjoint (supportComplementProjection U) := by
  exact cc20PositiveHalfLineProjection_isSelfAdjoint.sub
    (cc20TransportedSoninProjection_isSelfAdjoint U)

theorem supportComplementProjection_isIdempotentElem
    (U : H ≃ₗᵢ[ℂ] H) :
    IsIdempotentElem (supportComplementProjection U) := by
  apply ContinuousLinearMap.ext
  intro u
  unfold supportComplementProjection
  simp only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [show cc20PositiveHalfLineProjection
      (cc20PositiveHalfLineProjection u) =
        cc20PositiveHalfLineProjection u by
      exact cc20PositiveHalfLineProjection_idempotent u]
  rw [show cc20PositiveHalfLineProjection
      (cc20TransportedSoninProjection U u) =
        cc20TransportedSoninProjection U u by
      exact DFunLike.congr_fun
        (cc20PositiveHalfLineProjection_comp_sonin U) u]
  rw [show cc20TransportedSoninProjection U
      (cc20PositiveHalfLineProjection u) =
        cc20TransportedSoninProjection U u by
      exact DFunLike.congr_fun
        (cc20TransportedSonin_comp_positiveHalfLineProjection U) u]
  rw [show cc20TransportedSoninProjection U
      (cc20TransportedSoninProjection U u) =
        cc20TransportedSoninProjection U u by
      exact DFunLike.congr_fun
        (cc20TransportedSoninProjection_isStarProjection U
          |>.isIdempotentElem) u]
  abel

theorem supportComplementProjection_isStarProjection
    (U : H ≃ₗᵢ[ℂ] H) :
    IsStarProjection (supportComplementProjection U) :=
  ⟨supportComplementProjection_isIdempotentElem U,
    supportComplementProjection_isSelfAdjoint U⟩

theorem prolateFactor_adjoint_comp_self
    (U : H ≃ₗᵢ[ℂ] H) :
    (prolateFactor U).adjoint ∘L prolateFactor U =
      cc20TransportedProlateRemainder U := by
  rw [cc20TransportedProlateRemainder_eq_complement_conjugation]
  unfold prolateFactor supportComplementProjection
  rw [ContinuousLinearMap.adjoint_comp]
  rw [(cc20TransportedHalfLineProjection_isSelfAdjoint U).adjoint_eq]
  rw [map_sub,
    cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq,
    (cc20TransportedSoninProjection_isSelfAdjoint U).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hidempotent := congrArg
    (fun map : H →L[ℂ] H => map
      ((cc20PositiveHalfLineProjection -
        cc20TransportedSoninProjection U) u))
    (cc20TransportedHalfLineProjection_isStarProjection U
      |>.isIdempotentElem)
  exact congrArg
    (cc20PositiveHalfLineProjection -
      cc20TransportedSoninProjection U)
    (by simpa only [ContinuousLinearMap.mul_apply] using hidempotent)

theorem supportComplementProjection_comp_prolateFactor
    (U : H ≃ₗᵢ[ℂ] H) :
    supportComplementProjection U ∘L prolateFactor U =
      cc20TransportedProlateRemainder U := by
  rw [cc20TransportedProlateRemainder_eq_complement_conjugation]
  rfl

/-- The canonical defect is the raw crossing of the two original support
projections.  The Sonin projection cancels exactly before any estimate. -/
theorem prolateDefectFactor_eq_rawSupportCrossing
    (U : H ≃ₗᵢ[ℂ] H) :
    prolateDefectFactor U =
      (ContinuousLinearMap.id ℂ H - cc20PositiveHalfLineProjection) ∘L
        cc20TransportedHalfLineProjection U ∘L
          cc20PositiveHalfLineProjection := by
  apply ContinuousLinearMap.ext
  intro u
  unfold prolateDefectFactor prolateFactor supportComplementProjection
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub,
    ContinuousLinearMap.id_apply]
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
        (cc20TransportedSoninProjection_isStarProjection U
          |>.isIdempotentElem) u]
  abel

theorem prolateDefectFactor_adjoint_comp_self
    (U : H ≃ₗᵢ[ℂ] H) :
    (prolateDefectFactor U).adjoint ∘L prolateDefectFactor U =
      cc20TransportedProlateRemainder U -
        (cc20TransportedProlateRemainder U).adjoint ∘L
          cc20TransportedProlateRemainder U := by
  let B := supportComplementProjection U
  let A := prolateFactor U
  let K := cc20TransportedProlateRemainder U
  have hBself : B.adjoint = B :=
    (supportComplementProjection_isSelfAdjoint U).adjoint_eq
  have hAgram : A.adjoint ∘L A = K :=
    prolateFactor_adjoint_comp_self U
  have hBA : B ∘L A = K :=
    supportComplementProjection_comp_prolateFactor U
  have hAdjointBA := congrArg ContinuousLinearMap.adjoint hBA
  have hAadjB : A.adjoint ∘L B = K.adjoint := by
    simpa only [ContinuousLinearMap.adjoint_comp, hBself] using hAdjointBA
  have hBidem : IsIdempotentElem B :=
    supportComplementProjection_isIdempotentElem U
  unfold prolateDefectFactor
  change ((ContinuousLinearMap.id ℂ H - B) ∘L A).adjoint ∘L
      ((ContinuousLinearMap.id ℂ H - B) ∘L A) =
    K - K.adjoint ∘L K
  rw [ContinuousLinearMap.adjoint_comp, map_sub,
    ContinuousLinearMap.adjoint_id, hBself]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub,
    ContinuousLinearMap.id_apply]
  have hAgramAt : A.adjoint (A u) = K u := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun hAgram u
  have hBAAt : B (A u) = K u := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun hBA u
  have hBidemAt := congrArg
    (fun map : H →L[ℂ] H => map (A u)) hBidem
  simp only [ContinuousLinearMap.mul_apply] at hBidemAt
  have hKsqAt := DFunLike.congr_fun hAadjB (B (A u))
  simp only [ContinuousLinearMap.comp_apply] at hKsqAt
  rw [hBidemAt, hBAAt] at hKsqAt
  rw [hBidemAt, hAgramAt, hBAAt, hKsqAt]
  abel

theorem prolateFactor_summable_of_strictAngle
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (U : H ≃ₗᵢ[ℂ] H)
    (hangle : ‖prolateFactor U‖ < 1)
    (hdefect : Summable fun i =>
      ‖prolateDefectFactor U (basis i)‖ ^ 2) :
    Summable fun i => ‖prolateFactor U (basis i)‖ ^ 2 := by
  have hdefectIdentity :
      (prolateDefectFactor U).adjoint ∘L prolateDefectFactor U =
        (prolateFactor U).adjoint ∘L prolateFactor U -
          ((prolateFactor U).adjoint ∘L prolateFactor U).adjoint ∘L
            ((prolateFactor U).adjoint ∘L prolateFactor U) := by
    rw [prolateFactor_adjoint_comp_self]
    exact prolateDefectFactor_adjoint_comp_self U
  exact summable_normSq_of_strictContraction_of_defect basis
    (prolateFactor U) (prolateDefectFactor U) hangle
      hdefectIdentity hdefect

theorem prolateRemainder_isTraceClassAlong_of_strictAngle
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (U : H ≃ₗᵢ[ℂ] H)
    (hangle : ‖prolateFactor U‖ < 1)
    (hdefect : Summable fun i =>
      ‖prolateDefectFactor U (basis i)‖ ^ 2) :
    IsTraceClassAlong basis (cc20TransportedProlateRemainder U) := by
  let data : BasisHilbertSchmidtData basis :=
    { operator := prolateFactor U
      summable_normSq :=
        prolateFactor_summable_of_strictAngle basis U hangle hdefect }
  rw [← prolateFactor_adjoint_comp_self U]
  exact data.positiveComposition_isTraceClassAlong

end ProlateTraceReduction
end CC20Concrete
end Source
end ConnesWeilRH
