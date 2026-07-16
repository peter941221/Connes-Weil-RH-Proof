/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootSandwichedMovingFlow

/-!
# Calculus of the root-sandwiched moving projection

The selected root is fixed while the canonical Gram projection moves.  This
module differentiates the complete root-sandwiched operator in operator norm
and identifies its derivative with the legal completed crossing owner.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootSandwichedProjectionCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSActualMovingProjection
open CCM24FiniteSBandTrace
open CCM24FiniteSRootSandwichedMovingFlow

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- A fixed root sandwich of an ambient operator. -/
noncomputable def rootSandwichedProjection (root P : Op) : Op :=
  root ∘L P ∘L root.adjoint

/-- Differentiating a fixed root sandwich only differentiates its middle
operator. -/
theorem hasDerivAt_rootSandwichedProjection
    (root : Op) {projection : ℝ → Op} {projectionDerivative : Op}
    {alpha : ℝ}
    (hprojection : HasDerivAt projection projectionDerivative alpha) :
    HasDerivAt
      (fun beta => rootSandwichedProjection root (projection beta))
      (root ∘L projectionDerivative ∘L root.adjoint) alpha := by
  have hroot : HasDerivAt (fun _ : ℝ => root) 0 alpha :=
    hasDerivAt_const alpha root
  have hrootAdjoint :
      HasDerivAt (fun _ : ℝ => root.adjoint) 0 alpha :=
    hasDerivAt_const alpha root.adjoint
  have hleft := HasDerivAt.complexCLMComp hroot hprojection
  have hall := HasDerivAt.complexCLMComp hleft hrootAdjoint
  simpa only [rootSandwichedProjection,
    ContinuousLinearMap.zero_comp, zero_add,
    ContinuousLinearMap.comp_zero, add_zero] using hall

/-- The actual selected root-sandwiched moving Sonin projection. -/
noncomputable def actualRootSandwichedSoninProjection
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  rootSandwichedProjection (rootConvolution owner)
    (parameterizedCanonicalGramProjection lambda alpha S)

/-- Its literal operator-norm derivative is the completed moving Sonin root
flow, not a finite-matrix covariance surrogate. -/
theorem hasDerivAt_actualRootSandwichedSoninProjection
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ =>
        actualRootSandwichedSoninProjection owner lambda beta S)
      (actualMovingSoninRootFlow owner lambda alpha S) alpha := by
  simpa only [actualRootSandwichedSoninProjection,
    actualMovingSoninRootFlow, rootSandwichedOrthogonalFlow] using
    hasDerivAt_rootSandwichedProjection (rootConvolution owner)
      (hasDerivAt_parameterizedCanonicalGramProjection_orthogonalFlow
        lambda alpha S halpha)

/-- Endpoint readback to the actual finite-S semilocal Sonin projection. -/
theorem actualRootSandwichedSoninProjection_one
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    actualRootSandwichedSoninProjection owner lambda 1 S =
      rootConvolution owner ∘L
        (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule.starProjection ∘L
        (rootConvolution owner).adjoint := by
  rw [actualRootSandwichedSoninProjection, rootSandwichedProjection,
    parameterizedCanonicalGramProjection_one]

end CCM24FiniteSRootSandwichedProjectionCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
