/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GramCorrectedSoninTransport

/-!
# CCM24 Sonin transport projection bridge

CCM24 transports the complete Sonin intersection by a bounded invertible map.
It does not transport either support projection by a unitary conjugation.
This module consumes exactly that intersection-level statement and identifies
the Gram-corrected transported projection with the canonical target
orthogonal projection.
-/

namespace ConnesWeilRH
namespace CC20Concrete

/--
The operator-level data needed to consume CCM24 Theorem 4.6.

`maps_sonin_intersection` concerns the complete intersection only. No field
claims that `theta` maps either support subspace separately.
-/
structure CCM24SoninTransportData
    (𝕜 H K : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] where
  sourceSupport : ClosedSubmodule 𝕜 H
  sourceFourierSupport : ClosedSubmodule 𝕜 H
  targetSupport : ClosedSubmodule 𝕜 K
  targetFourierSupport : ClosedSubmodule 𝕜 K
  theta : H ≃L[𝕜] K
  maps_sonin_intersection :
    transportedClosedSubmodule theta
        (sourceSupport ⊓ sourceFourierSupport) =
      targetSupport ⊓ targetFourierSupport

namespace CCM24SoninTransportData

variable {𝕜 H K : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The source complete Sonin intersection. -/
def sourceSoninClosedSubspace
    (D : CCM24SoninTransportData 𝕜 H K) : ClosedSubmodule 𝕜 H :=
  D.sourceSupport ⊓ D.sourceFourierSupport

/-- The actual target complete Sonin intersection. -/
def targetSoninClosedSubspace
    (D : CCM24SoninTransportData 𝕜 H K) : ClosedSubmodule 𝕜 K :=
  D.targetSupport ⊓ D.targetFourierSupport

@[simp]
theorem transported_sourceSonin_eq_targetSonin
    (D : CCM24SoninTransportData 𝕜 H K) :
    transportedClosedSubmodule D.theta D.sourceSoninClosedSubspace =
      D.targetSoninClosedSubspace := by
  exact D.maps_sonin_intersection

section Complete

variable [CompleteSpace H] [CompleteSpace K]

/-- The Gram-corrected projection obtained by restricting `theta` to the
source complete Sonin intersection. -/
noncomputable def gramCorrectedTargetSoninProjection
    (D : CCM24SoninTransportData 𝕜 H K) : K →L[𝕜] K :=
  transportedSoninStarProjection D.theta D.sourceSoninClosedSubspace

theorem gramCorrectedTargetSoninProjection_isStarProjection
    (D : CCM24SoninTransportData 𝕜 H K) :
    IsStarProjection D.gramCorrectedTargetSoninProjection := by
  exact transportedSoninStarProjection_isStarProjection
    D.theta D.sourceSoninClosedSubspace

theorem gramCorrectedTargetSoninProjection_range
    (D : CCM24SoninTransportData 𝕜 H K) :
    D.gramCorrectedTargetSoninProjection.range =
      D.targetSoninClosedSubspace.toSubmodule := by
  rw [gramCorrectedTargetSoninProjection,
    transportedSoninStarProjection_range,
    transported_sourceSonin_eq_targetSonin]

/-- The canonical orthogonal projection of the actual target Sonin
intersection. -/
noncomputable def targetSoninProjection
    (D : CCM24SoninTransportData 𝕜 H K) : K →L[𝕜] K :=
  D.targetSoninClosedSubspace.toSubmodule.starProjection

omit [CompleteSpace H] in
theorem targetSoninProjection_isStarProjection
    (D : CCM24SoninTransportData 𝕜 H K) :
    IsStarProjection D.targetSoninProjection := by
  exact isStarProjection_starProjection

/-- The Gram formula and the canonical target projection are the same
operator, not merely operators with isomorphic ranges. -/
theorem gramCorrectedTargetSoninProjection_eq_targetSoninProjection
    (D : CCM24SoninTransportData 𝕜 H K) :
    D.gramCorrectedTargetSoninProjection = D.targetSoninProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext
    D.gramCorrectedTargetSoninProjection_isStarProjection
    D.targetSoninProjection_isStarProjection
  rw [gramCorrectedTargetSoninProjection_range, targetSoninProjection,
    Submodule.range_starProjection]

/-- The Proof 315 factor identity instantiated on the actual target
subspaces, with the Gram-corrected Sonin projection as the intersection
term. -/
theorem target_compression_sub_gramCorrected_eq_factor
    (D : CCM24SoninTransportData 𝕜 H K) :
    D.targetSupport.toSubmodule.starProjection ∘L
          D.targetFourierSupport.toSubmodule.starProjection ∘L
          D.targetSupport.toSubmodule.starProjection -
        D.gramCorrectedTargetSoninProjection =
      (D.targetSupport.toSubmodule.starProjection -
          D.gramCorrectedTargetSoninProjection) ∘L
        D.targetFourierSupport.toSubmodule.starProjection ∘L
        (D.targetSupport.toSubmodule.starProjection -
          D.gramCorrectedTargetSoninProjection) := by
  letI : CompleteSpace
      ((D.targetSupport.toSubmodule ⊓
        D.targetFourierSupport.toSubmodule) : Submodule 𝕜 K) :=
    (D.targetSupport ⊓ D.targetFourierSupport).isClosed.completeSpace_coe
  rw [D.gramCorrectedTargetSoninProjection_eq_targetSoninProjection]
  simpa [targetSoninProjection, targetSoninClosedSubspace] using
    (compressed_projection_sub_intersection_eq_factor
      D.targetSupport.toSubmodule D.targetFourierSupport.toSubmodule)

/-- The target compression minus the transported Sonin projection is
positive without treating `theta` as unitary. -/
theorem target_compression_sub_gramCorrected_isPositive
    (D : CCM24SoninTransportData 𝕜 H K) :
    (D.targetSupport.toSubmodule.starProjection ∘L
          D.targetFourierSupport.toSubmodule.starProjection ∘L
          D.targetSupport.toSubmodule.starProjection -
        D.gramCorrectedTargetSoninProjection).IsPositive := by
  letI : CompleteSpace
      ((D.targetSupport.toSubmodule ⊓
        D.targetFourierSupport.toSubmodule) : Submodule 𝕜 K) :=
    (D.targetSupport ⊓ D.targetFourierSupport).isClosed.completeSpace_coe
  rw [D.gramCorrectedTargetSoninProjection_eq_targetSoninProjection]
  simpa [targetSoninProjection, targetSoninClosedSubspace] using
    (compressed_projection_sub_intersection_isPositive
      D.targetSupport.toSubmodule D.targetFourierSupport.toSubmodule)

end Complete

end CCM24SoninTransportData
end CC20Concrete
end ConnesWeilRH
