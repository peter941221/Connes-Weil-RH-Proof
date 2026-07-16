/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24SoninProjectionBridge

/-!
# Restricted CCM24 Sonin equivalence

CCM24 Theorem 4.6 states that `theta_S` induces a hilbertian isomorphism
between the complete source and semilocal Sonin spaces. This module packages
that restricted equivalence and its ambient compatibility, then derives the
closed-subspace image equality consumed by `CCM24SoninTransportData`.

No field claims that `theta_S` transports either support subspace separately.
-/

namespace ConnesWeilRH
namespace CC20Concrete

/--
The source-shaped form of CCM24 Theorem 4.6: an ambient bounded equivalence
whose restriction is a bounded equivalence of the complete Sonin spaces.

The compatibility field is the commutative inclusion diagram. It is imposed
only on the complete intersections, not on either support subspace alone.
-/
structure CCM24RestrictedSoninEquivData
    (𝕜 H K : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] where
  sourceSupport : ClosedSubmodule 𝕜 H
  sourceFourierSupport : ClosedSubmodule 𝕜 H
  targetSupport : ClosedSubmodule 𝕜 K
  targetFourierSupport : ClosedSubmodule 𝕜 K
  theta : H ≃L[𝕜] K
  restrictedTheta :
    (sourceSupport ⊓ sourceFourierSupport).toSubmodule ≃L[𝕜]
      (targetSupport ⊓ targetFourierSupport).toSubmodule
  restrictedTheta_coe : ∀ x,
    ((restrictedTheta x :
      (targetSupport ⊓ targetFourierSupport).toSubmodule) : K) = theta x

namespace CCM24RestrictedSoninEquivData

variable {𝕜 H K : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The restricted CCM24 equivalence implies the exact ambient image equality
for the complete Sonin intersections. -/
theorem maps_sonin_intersection
    (D : CCM24RestrictedSoninEquivData 𝕜 H K) :
    transportedClosedSubmodule D.theta
        (D.sourceSupport ⊓ D.sourceFourierSupport) =
      D.targetSupport ⊓ D.targetFourierSupport := by
  ext y
  constructor
  · intro hy
    have hsource : D.theta.symm y ∈
        D.sourceSupport ⊓ D.sourceFourierSupport :=
      (ClosedSubmodule.mem_mapEquiv_iff D.theta
        (D.sourceSupport ⊓ D.sourceFourierSupport) y).1 hy
    let x : (D.sourceSupport ⊓ D.sourceFourierSupport).toSubmodule :=
      ⟨D.theta.symm y, hsource⟩
    have hcoe :
        ((D.restrictedTheta x :
          (D.targetSupport ⊓ D.targetFourierSupport).toSubmodule) : K) = y := by
      rw [D.restrictedTheta_coe]
      simp [x]
    rw [← hcoe]
    exact (D.restrictedTheta x).property
  · intro hy
    let y' : (D.targetSupport ⊓ D.targetFourierSupport).toSubmodule := ⟨y, hy⟩
    let x : (D.sourceSupport ⊓ D.sourceFourierSupport).toSubmodule :=
      D.restrictedTheta.symm y'
    have htheta : D.theta x = y := by
      rw [← D.restrictedTheta_coe]
      exact congrArg Subtype.val (D.restrictedTheta.apply_symm_apply y')
    rw [← htheta]
    exact (ClosedSubmodule.mem_mapEquiv_iff' D.theta
      (D.sourceSupport ⊓ D.sourceFourierSupport) x).2 x.property

/-- Convert the source theorem's restricted-isomorphism form into the
intersection-image interface consumed by the Gram-corrected projection. -/
def toSoninTransportData
    (D : CCM24RestrictedSoninEquivData 𝕜 H K) :
    CCM24SoninTransportData 𝕜 H K where
  sourceSupport := D.sourceSupport
  sourceFourierSupport := D.sourceFourierSupport
  targetSupport := D.targetSupport
  targetFourierSupport := D.targetFourierSupport
  theta := D.theta
  maps_sonin_intersection := D.maps_sonin_intersection

@[simp]
theorem toSoninTransportData_sourceSoninClosedSubspace
    (D : CCM24RestrictedSoninEquivData 𝕜 H K) :
    D.toSoninTransportData.sourceSoninClosedSubspace =
      D.sourceSupport ⊓ D.sourceFourierSupport := rfl

@[simp]
theorem toSoninTransportData_targetSoninClosedSubspace
    (D : CCM24RestrictedSoninEquivData 𝕜 H K) :
    D.toSoninTransportData.targetSoninClosedSubspace =
      D.targetSupport ⊓ D.targetFourierSupport := rfl

section Complete

variable [CompleteSpace H] [CompleteSpace K]

/-- The source-shaped CCM24 theorem produces the canonical target Sonin
projection through the Gram-corrected transport formula. -/
theorem gramCorrectedTargetSoninProjection_eq_targetSoninProjection
    (D : CCM24RestrictedSoninEquivData 𝕜 H K) :
    D.toSoninTransportData.gramCorrectedTargetSoninProjection =
      D.toSoninTransportData.targetSoninProjection :=
  D.toSoninTransportData.gramCorrectedTargetSoninProjection_eq_targetSoninProjection

/-- The complete target compression is positive after consuming the actual
restricted CCM24 Sonin equivalence. -/
theorem target_compression_sub_gramCorrected_isPositive
    (D : CCM24RestrictedSoninEquivData 𝕜 H K) :
    (D.targetSupport.toSubmodule.starProjection ∘L
          D.targetFourierSupport.toSubmodule.starProjection ∘L
          D.targetSupport.toSubmodule.starProjection -
        D.toSoninTransportData.gramCorrectedTargetSoninProjection).IsPositive :=
  D.toSoninTransportData.target_compression_sub_gramCorrected_isPositive

end Complete

end CCM24RestrictedSoninEquivData
end CC20Concrete
end ConnesWeilRH
