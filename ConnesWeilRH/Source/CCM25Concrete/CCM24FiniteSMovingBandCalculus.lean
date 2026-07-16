/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedZeroEndpoint
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootSandwichedProjectionCalculus

/-!
# Actual moving finite-S Sonin band

The fixed radial support projection minus the moving canonical Sonin
projection gives a proof-independent path from the source band to the actual
finite-S band.  Its selected root sandwich differentiates to the negative
completed Sonin flow and its endpoint difference is the repository's existing
same-object band response.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSActualMovingProjection
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSBandTrace
open CCM24FiniteSRootSandwichedMovingFlow
open CCM24FiniteSRootSandwichedProjectionCalculus
open CCM24FiniteSParameterizedZeroEndpoint

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The actual moving orthogonal Sonin band `B_alpha=E-R_alpha`. -/
noncomputable def parameterizedSoninBand
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  radialSupportProjection lambda -
    parameterizedCanonicalGramProjection lambda alpha S

/-- The moving band derivative is the negative completed Sonin projection
flow because the radial support projection is fixed. -/
theorem hasDerivAt_parameterizedSoninBand
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ => parameterizedSoninBand lambda beta S)
      (-orthogonalProjectionDerivative
        (parameterizedCanonicalGramProjection lambda alpha S)
        (CCM24FiniteSParameterizedEulerGenerator.parameterizedFiniteEulerGenerator
          alpha S)) alpha := by
  have hradial : HasDerivAt
      (fun _ : ℝ => radialSupportProjection lambda) 0 alpha :=
    hasDerivAt_const alpha (radialSupportProjection lambda)
  have hsonin :=
    hasDerivAt_parameterizedCanonicalGramProjection_orthogonalFlow
      lambda alpha S halpha
  simpa only [parameterizedSoninBand, zero_sub] using hradial.sub hsonin

/-- Source endpoint of the actual band path. -/
theorem parameterizedSoninBand_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedSoninBand lambda 0 S = sourceBandProjection lambda := by
  rw [parameterizedSoninBand,
    parameterizedCanonicalGramProjection_zero]
  rfl

/-- Finite-S endpoint of the actual band path, with the visible-prime list
owned by the same arithmetic family. -/
theorem parameterizedSoninBand_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    parameterizedSoninBand lambda 1 family.visiblePrimes =
      targetBandProjection lambda family := by
  rw [parameterizedSoninBand,
    CCM24FiniteSActualMovingProjection.parameterizedCanonicalGramProjection_one]
  rfl

/-- The selected root sandwich of the actual moving band. -/
noncomputable def actualRootSandwichedSoninBand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  rootSandwichedProjection (rootConvolution owner)
    (parameterizedSoninBand lambda alpha S)

/-- Its operator-norm derivative is the negative completed root-smoothed
Sonin flow. -/
theorem hasDerivAt_actualRootSandwichedSoninBand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ =>
        actualRootSandwichedSoninBand owner lambda beta S)
      (-actualMovingSoninRootFlow owner lambda alpha S) alpha := by
  have h := hasDerivAt_rootSandwichedProjection (rootConvolution owner)
    (hasDerivAt_parameterizedSoninBand lambda alpha S halpha)
  simpa only [actualRootSandwichedSoninBand,
    actualMovingSoninRootFlow, rootSandwichedOrthogonalFlow,
    ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_comp] using h

/-- The path endpoint difference is literally the pre-existing same-object
root-sandwiched finite-S band response. -/
theorem actualRootSandwichedSoninBand_one_sub_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualRootSandwichedSoninBand owner lambda 1 family.visiblePrimes -
        actualRootSandwichedSoninBand owner lambda 0 family.visiblePrimes =
      rootSandwichedBandResponse owner lambda family := by
  rw [actualRootSandwichedSoninBand, actualRootSandwichedSoninBand,
    parameterizedSoninBand_one, parameterizedSoninBand_zero,
    rootSandwichedBandResponse, soninBandDifference]
  unfold rootSandwichedProjection
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]

end CCM24FiniteSMovingBandCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
