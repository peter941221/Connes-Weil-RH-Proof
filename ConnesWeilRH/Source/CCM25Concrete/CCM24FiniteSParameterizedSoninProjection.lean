/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedSoninSubspace
import ConnesWeilRH.Source.CC20Concrete.GramCorrectedSoninTransport

/-!
# Parameterized finite-S Sonin projection

Each synchronized time slice uses the canonical orthogonal projection onto
the actual moving Sonin intersection.  The projection is identified with the
Gram-corrected bounded-invertible transport; no oblique similarity is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedSoninProjection

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedSoninSubspace
open _root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData

/-- The moving second-support orthogonal projection. -/
noncomputable def parameterizedFourierSupportProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (parameterizedFourierSupportClosedSubspace lambda alpha S halpha)
    |>.toSubmodule.starProjection

/-- The canonical moving complete-Sonin orthogonal projection. -/
noncomputable def parameterizedSoninProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (parameterizedSoninClosedSubspace lambda alpha S halpha)
    |>.toSubmodule.starProjection

theorem parameterizedFourierSupportProjection_isStarProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsStarProjection
      (parameterizedFourierSupportProjection lambda alpha S halpha) :=
  isStarProjection_starProjection

/-- The moving second-support projection is the Gram-corrected orthogonal
projection onto the bounded-invertible image of the source Fourier-support
space.  It is not the oblique similarity `T Q T^-1`. -/
theorem parameterizedFourierSupportProjection_eq_gramCorrectedTransport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFourierSupportProjection lambda alpha S halpha =
      _root_.ConnesWeilRH.CC20Concrete.transportedSoninStarProjection
        (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda) := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (parameterizedFourierSupportProjection_isStarProjection
      lambda alpha S halpha)
    (_root_.ConnesWeilRH.CC20Concrete.transportedSoninStarProjection_isStarProjection
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda))
  unfold parameterizedFourierSupportProjection
  rw [Submodule.range_starProjection,
    _root_.ConnesWeilRH.CC20Concrete.transportedSoninStarProjection_range]
  rw [_root_.ConnesWeilRH.CC20Concrete.transportedClosedSubmodule]
  exact congrArg
    (fun P : ClosedSubmodule ℂ finiteSCarrier => P.toSubmodule)
    (parameterizedFiniteEulerEquiv_maps_fourierSupport
      lambda alpha S halpha).symm

theorem parameterizedSoninProjection_isStarProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsStarProjection
      (parameterizedSoninProjection lambda alpha S halpha) :=
  isStarProjection_starProjection

/-- Exact Proof 317 datum for a synchronized time slice. -/
noncomputable def parameterizedSoninTransportData
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    _root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData
      ℂ finiteSCarrier finiteSCarrier where
  sourceSupport := ccm24LogRadialSupportClosedSubspace lambda
  sourceFourierSupport :=
    ccm24ArchimedeanFourierSupportClosedSubspace lambda
  targetSupport := ccm24LogRadialSupportClosedSubspace lambda
  targetFourierSupport :=
    parameterizedFourierSupportClosedSubspace lambda alpha S halpha
  theta := parameterizedFiniteEulerEquiv alpha S halpha
  maps_sonin_intersection := by
    simpa [ccm24ArchimedeanSoninClosedSubspace,
      parameterizedSoninClosedSubspace,
      _root_.ConnesWeilRH.CC20Concrete.transportedClosedSubmodule] using
      parameterizedFiniteEulerEquiv_maps_sonin
        lambda alpha S halpha

/-- The moving canonical projection is exactly the Gram-corrected frame
operator of the actual synchronized transport. -/
theorem parameterizedSoninProjection_eq_gramCorrected
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedSoninProjection lambda alpha S halpha =
      gramCorrectedTargetSoninProjection
        (parameterizedSoninTransportData lambda alpha S halpha) := by
  symm
  exact gramCorrectedTargetSoninProjection_eq_targetSoninProjection
    (parameterizedSoninTransportData lambda alpha S halpha)

/-- The full moving prolate remainder. -/
noncomputable def parameterizedProlateRemainder
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
      parameterizedFourierSupportProjection lambda alpha S halpha ∘L
      radialSupportProjection lambda -
    parameterizedSoninProjection lambda alpha S halpha

/-- Exact positive factorization of the moving prolate remainder. -/
theorem parameterizedProlateRemainder_eq_factor
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedProlateRemainder lambda alpha S halpha =
      (radialSupportProjection lambda -
          parameterizedSoninProjection lambda alpha S halpha) ∘L
        parameterizedFourierSupportProjection lambda alpha S halpha ∘L
        (radialSupportProjection lambda -
          parameterizedSoninProjection lambda alpha S halpha) := by
  rw [parameterizedProlateRemainder,
    parameterizedSoninProjection_eq_gramCorrected]
  simpa [radialSupportProjection,
    parameterizedFourierSupportProjection,
    parameterizedSoninTransportData] using
    (target_compression_sub_gramCorrected_eq_factor
      (parameterizedSoninTransportData lambda alpha S halpha))

theorem parameterizedProlateRemainder_isPositive
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (parameterizedProlateRemainder lambda alpha S halpha).IsPositive := by
  rw [parameterizedProlateRemainder,
    parameterizedSoninProjection_eq_gramCorrected]
  simpa [radialSupportProjection,
    parameterizedFourierSupportProjection,
    parameterizedSoninTransportData] using
    (target_compression_sub_gramCorrected_isPositive
      (parameterizedSoninTransportData lambda alpha S halpha))

/-- At time one the moving Hardy--Titchmarsh involution is the existing
finite-S semilocal involution. -/
theorem parameterizedSemilocalHardyTitchmarsh_one
    (S : List CCM24VisiblePrime) :
    parameterizedSemilocalHardyTitchmarsh 1 S (by norm_num) =
      ccm24SemilocalHardyTitchmarsh S := by
  unfold parameterizedSemilocalHardyTitchmarsh
    ccm24SemilocalHardyTitchmarsh
  rw [parameterizedFiniteEulerEquiv_one]

/-- Endpoint equality for the actual Fourier-support closed subspace. -/
theorem parameterizedFourierSupportClosedSubspace_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedFourierSupportClosedSubspace lambda 1 S (by norm_num) =
      ccm24SemilocalFourierSupportClosedSubspace lambda S := by
  unfold parameterizedFourierSupportClosedSubspace
    ccm24SemilocalFourierSupportClosedSubspace
  rw [parameterizedSemilocalHardyTitchmarsh_one]

/-- Endpoint equality for the complete Sonin intersection. -/
theorem parameterizedSoninClosedSubspace_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedSoninClosedSubspace lambda 1 S (by norm_num) =
      ccm24SemilocalSoninClosedSubspace lambda S := by
  unfold parameterizedSoninClosedSubspace
    ccm24SemilocalSoninClosedSubspace
  rw [parameterizedFourierSupportClosedSubspace_one]

/-- The canonical moving projection lands at the repository's actual finite-S
Sonin projection. -/
theorem parameterizedSoninProjection_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedSoninProjection lambda 1 S (by norm_num) =
      (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule.starProjection := by
  unfold parameterizedSoninProjection
  apply ContinuousLinearMap.IsStarProjection.ext
    isStarProjection_starProjection isStarProjection_starProjection
  rw [Submodule.range_starProjection, Submodule.range_starProjection]
  exact congrArg (fun P : ClosedSubmodule ℂ finiteSCarrier => P.toSubmodule)
    (parameterizedSoninClosedSubspace_one lambda S)

end CCM24FiniteSParameterizedSoninProjection
end CCM25Concrete
end Source
end ConnesWeilRH
