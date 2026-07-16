/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedInverseCalculus

/-!
# Real calculus of adjoint operator paths

Although adjoint is conjugate-linear over `C`, it is linear and isometric over
`R`.  This module packages that exact real linear isometry and transports the
Euler product derivatives through adjoint without an informal conjugation
step.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSAdjointCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerCalculus
open CCM24FiniteSParameterizedInverseCalculus

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- Adjoint as a real linear isometry of the actual common-log operator
space. -/
noncomputable def adjointRealLinearIsometry : Op →ₗᵢ[ℝ] Op where
  toFun := ContinuousLinearMap.adjoint
  map_add' A B := map_add ContinuousLinearMap.adjoint A B
  map_smul' r A := by
    change ContinuousLinearMap.adjoint ((r : ℂ) • A) =
      (r : ℂ) • ContinuousLinearMap.adjoint A
    rw [map_smulₛₗ]
    simp
  norm_map' A := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint A

@[simp]
theorem adjointRealLinearIsometry_apply (A : Op) :
    adjointRealLinearIsometry A = ContinuousLinearMap.adjoint A :=
  rfl

/-- Differentiation commutes with adjoint for real-parameter operator paths. -/
theorem HasDerivAt.adjoint
    {f : ℝ → Op} {f' : Op} {alpha : ℝ}
    (hf : HasDerivAt f f' alpha) :
    HasDerivAt (fun beta => ContinuousLinearMap.adjoint (f beta))
      (ContinuousLinearMap.adjoint f') alpha := by
  simpa only [Function.comp_apply, adjointRealLinearIsometry_apply] using
    adjointRealLinearIsometry.toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt alpha hf

/-- Adjoint synchronized Euler product derivative. -/
theorem hasDerivAt_adjoint_parameterizedFiniteEulerFactor
    (alpha : ℝ) (S : List CCM24VisiblePrime) :
    HasDerivAt
      (fun beta : ℝ => ContinuousLinearMap.adjoint
        (parameterizedFiniteEulerFactor beta S))
      (ContinuousLinearMap.adjoint
        (parameterizedFiniteEulerDerivative alpha S)) alpha :=
  HasDerivAt.adjoint
    (hasDerivAt_parameterizedFiniteEulerFactor alpha S)

/-- Adjoint inverse derivative on the interior synchronized interval. -/
theorem hasDerivAt_adjoint_parameterizedFiniteEulerInverse
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| < 1) :
    HasDerivAt
      (fun beta : ℝ => ContinuousLinearMap.adjoint
        (parameterizedFiniteEulerInverse beta S))
      (ContinuousLinearMap.adjoint
        (parameterizedFiniteEulerInverseDerivative alpha S)) alpha :=
  HasDerivAt.adjoint
    (hasDerivAt_parameterizedFiniteEulerInverse alpha S halpha)

end CCM24FiniteSAdjointCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
