/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CC20Concrete.CCM24RestrictedSoninEquiv

/-!
# Finite Euler transport restricted to the complete Sonin spaces

This module fixes the ambient map in the restricted CCM24 Sonin theorem to the
concrete finite Euler transport on the global logarithmic `L2` carrier. It
also fixes both radial support subspaces to the actual `t >= log lambda`
closed subspace. The remaining producer is the pair of genuine Fourier
support subspaces and the source theorem's restricted equivalence.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

/-- Source-shaped CCM24 Sonin data whose ambient map is the concrete finite
Euler transport, rather than an arbitrary bounded equivalence. -/
structure CCM24FiniteEulerRestrictedSoninData
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) where
  sourceFourierSupport : ClosedSubmodule ℂ cc20GlobalLogCrossingL2
  targetFourierSupport : ClosedSubmodule ℂ cc20GlobalLogCrossingL2
  restrictedTheta :
    (ccm24LogRadialSupportClosedSubspace lambda ⊓
        sourceFourierSupport).toSubmodule ≃L[ℂ]
      (ccm24LogRadialSupportClosedSubspace lambda ⊓
        targetFourierSupport).toSubmodule
  restrictedTheta_coe : ∀ x,
    ((restrictedTheta x :
      (ccm24LogRadialSupportClosedSubspace lambda ⊓
        targetFourierSupport).toSubmodule) :
        cc20GlobalLogCrossingL2) =
      ccm24FiniteEulerTransportEquiv S x

namespace CCM24FiniteEulerRestrictedSoninData

variable {lambda : CCM24SoninScale}
variable {S T : List CCM24VisiblePrime}

/-- Forget only the source-specific identification of the ambient operator;
the resulting generic restricted-Sonin datum still carries the same concrete
finite Euler equivalence. -/
noncomputable def toRestrictedSoninEquivData
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) :
    _root_.ConnesWeilRH.CC20Concrete.CCM24RestrictedSoninEquivData
      ℂ cc20GlobalLogCrossingL2 cc20GlobalLogCrossingL2 where
  sourceSupport := ccm24LogRadialSupportClosedSubspace lambda
  sourceFourierSupport := D.sourceFourierSupport
  targetSupport := ccm24LogRadialSupportClosedSubspace lambda
  targetFourierSupport := D.targetFourierSupport
  theta := ccm24FiniteEulerTransportEquiv S
  restrictedTheta := D.restrictedTheta
  restrictedTheta_coe := D.restrictedTheta_coe

@[simp]
theorem toRestrictedSoninEquivData_theta
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) :
    D.toRestrictedSoninEquivData.theta =
      ccm24FiniteEulerTransportEquiv S := rfl

/-- The restricted source theorem now proves the exact image equality for the
concrete finite Euler transport. -/
theorem maps_sonin_intersection
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) :
    _root_.ConnesWeilRH.CC20Concrete.transportedClosedSubmodule
        (ccm24FiniteEulerTransportEquiv S)
        (ccm24LogRadialSupportClosedSubspace lambda ⊓
          D.sourceFourierSupport) =
      ccm24LogRadialSupportClosedSubspace lambda ⊓
        D.targetFourierSupport :=
  D.toRestrictedSoninEquivData.maps_sonin_intersection

/-- The exact Proof 317 consumer data, now owned by the concrete finite Euler
operator on the global logarithmic carrier. -/
noncomputable def toSoninTransportData
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) :
    _root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData
      ℂ cc20GlobalLogCrossingL2 cc20GlobalLogCrossingL2 :=
  D.toRestrictedSoninEquivData.toSoninTransportData

@[simp]
theorem toSoninTransportData_theta
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) :
    D.toSoninTransportData.theta = ccm24FiniteEulerTransportEquiv S := rfl

/-- Reordering the visible places preserves the source theorem contract, not
only its ambient operator. -/
noncomputable def reindex
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) (h : S.Perm T) :
    CCM24FiniteEulerRestrictedSoninData lambda T where
  sourceFourierSupport := D.sourceFourierSupport
  targetFourierSupport := D.targetFourierSupport
  restrictedTheta := D.restrictedTheta
  restrictedTheta_coe := fun x => by
    rw [← ccm24FiniteEulerTransportEquiv_eq_of_perm h]
    exact D.restrictedTheta_coe x

/-- Proof 315 positivity instantiated with both the actual finite Euler
ambient transport and the actual restricted CCM24 Sonin equivalence. -/
theorem target_compression_sub_gramCorrected_isPositive
    (D : CCM24FiniteEulerRestrictedSoninData lambda S) :
    ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection ∘L
          D.targetFourierSupport.toSubmodule.starProjection ∘L
          (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection -
        D.toSoninTransportData.gramCorrectedTargetSoninProjection).IsPositive :=
  D.toRestrictedSoninEquivData.target_compression_sub_gramCorrected_isPositive

end CCM24FiniteEulerRestrictedSoninData
end CC20Concrete
end Source
end ConnesWeilRH
