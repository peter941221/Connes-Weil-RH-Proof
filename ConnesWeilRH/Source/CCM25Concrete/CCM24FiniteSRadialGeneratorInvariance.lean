/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedMovingCrossing

/-!
# Radial invariance of the complete Euler generator

Every one-sided prime-power generator preserves the fixed radial support.
Consequently its oriented crossing through the radial orthogonal projection
vanishes exactly.  The actual outer-minus-Sonin crossing therefore reduces to
the negative Sonin crossing before any trace or norm is taken.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRadialGeneratorInvariance

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedRadialSupport
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSCompletedMovingCrossing

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- A one-prime right logarithmic generator preserves the literal radial
support subspace. -/
theorem parameterizedPrimeEulerGenerator_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedPrimeEulerGenerator alpha p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  unfold parameterizedPrimeEulerGenerator
  simp only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.neg_apply]
  apply (ccm24LogRadialSupportClosedSubspace lambda).neg_mem
  exact ccm24PrimeEulerContraction_mem_logRadialSupport lambda p
    (parameterizedPrimeEulerInverse_mem_radialSupport
      lambda alpha p halpha hu)

/-- The complete finite-prime generator preserves radial support before any
primewise norm or absolute value is introduced. -/
theorem parameterizedFiniteEulerGenerator_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedFiniteEulerGenerator alpha S u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  induction S with
  | nil =>
      rw [parameterizedFiniteEulerGenerator_nil,
        ContinuousLinearMap.zero_apply]
      exact (ccm24LogRadialSupportClosedSubspace lambda).zero_mem
  | cons p S ih =>
      rw [parameterizedFiniteEulerGenerator_cons,
        ContinuousLinearMap.add_apply]
      exact (ccm24LogRadialSupportClosedSubspace lambda).add_mem
        (parameterizedPrimeEulerGenerator_mem_radialSupport
          lambda alpha p halpha hu)
        ih

/-- The complete Euler generator has no outward radial crossing. -/
theorem radial_projectionLeftCrossing_parameterizedGenerator_eq_zero
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    projectionLeftCrossing
        (radialSupportProjection lambda)
        (parameterizedFiniteEulerGenerator alpha S) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  unfold projectionLeftCrossing
  simp only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.zero_apply]
  have hprojected : radialSupportProjection lambda u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
    unfold radialSupportProjection
    exact Submodule.starProjection_apply_mem _ _
  have hgenerator :
      parameterizedFiniteEulerGenerator alpha S
          (radialSupportProjection lambda u) ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    parameterizedFiniteEulerGenerator_mem_radialSupport
      lambda alpha S halpha hprojected
  have hfixed : radialSupportProjection lambda
        (parameterizedFiniteEulerGenerator alpha S
          (radialSupportProjection lambda u)) =
      parameterizedFiniteEulerGenerator alpha S
        (radialSupportProjection lambda u) := by
    unfold radialSupportProjection
    exact Submodule.starProjection_eq_self_iff.mpr hgenerator
  rw [hfixed]
  exact sub_self _

/-- The actual signed crossing is just the negative moving Sonin crossing;
the fixed radial branch has disappeared by source geometry. -/
theorem actualSignedMovingCrossing_eq_neg_soninCrossing
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    signedProjectionLeftCrossing
        (radialSupportProjection lambda)
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S) =
      -projectionLeftCrossing
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S) := by
  unfold signedProjectionLeftCrossing
  rw [radial_projectionLeftCrossing_parameterizedGenerator_eq_zero
    lambda alpha S halpha]
  exact zero_sub _

/-- The recombined completed owner inherits the same four-branch reduction.
This theorem does not split or estimate the remaining terms. -/
theorem completedMovingCrossing_eq_neg_soninCrossing
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    completedMovingCrossing
        (radialSupportProjection lambda)
        (CCM24FiniteSParameterizedSoninProjection.parameterizedFourierSupportProjection
          lambda alpha S halpha)
        (CCM24FiniteSParameterizedSoninProjection.parameterizedProlateRemainder
          lambda alpha S halpha)
        (parameterizedFiniteEulerGenerator alpha S) =
      -projectionLeftCrossing
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S) := by
  rw [← actualSignedMovingCrossing_eq_completed lambda alpha S halpha]
  exact actualSignedMovingCrossing_eq_neg_soninCrossing
    lambda alpha S halpha

/-- Root smoothing is applied after the exact outer-branch deletion. -/
theorem rootSandwiched_completedMovingCrossing_eq_neg_soninCrossing
    (root : Op) (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    root ∘L completedMovingCrossing
        (radialSupportProjection lambda)
        (CCM24FiniteSParameterizedSoninProjection.parameterizedFourierSupportProjection
          lambda alpha S halpha)
        (CCM24FiniteSParameterizedSoninProjection.parameterizedProlateRemainder
          lambda alpha S halpha)
        (parameterizedFiniteEulerGenerator alpha S) ∘L root.adjoint =
      -(root ∘L projectionLeftCrossing
          (parameterizedCanonicalGramProjection lambda alpha S)
          (parameterizedFiniteEulerGenerator alpha S) ∘L root.adjoint) := by
  rw [completedMovingCrossing_eq_neg_soninCrossing
    lambda alpha S halpha]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg]

end CCM24FiniteSRadialGeneratorInvariance
end CCM25Concrete
end Source
end ConnesWeilRH
