/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedSoninProjection
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Calculus of the synchronized finite Euler product

The recursive product-rule operator is proved to be the actual norm
derivative of the synchronized Euler product.  The inverse product is also
identified with Banach-algebra inversion through a concrete unit.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedEulerCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct

/-- One synchronized Euler factor has constant derivative `-A_p`. -/
theorem hasDerivAt_parameterizedPrimeEulerFactor
    (alpha : ℝ) (p : CCM24VisiblePrime) :
    HasDerivAt (fun beta : ℝ => parameterizedPrimeEulerFactor beta p)
      (-ccm24PrimeEulerContraction p) alpha := by
  have hsmul : HasDerivAt
      (fun beta : ℝ => beta • ccm24PrimeEulerContraction p)
      (ccm24PrimeEulerContraction p) alpha := by
    simpa only [one_smul] using
      (hasDerivAt_id alpha).smul_const (ccm24PrimeEulerContraction p)
  have hsub := (hasDerivAt_const alpha
      (1 : finiteSCarrier →L[ℂ] finiteSCarrier)).sub hsmul
  convert hsub using 1
  simp

/-- The recursively defined product-rule operator is the actual derivative
of the complete synchronized Euler product. -/
theorem hasDerivAt_parameterizedFiniteEulerFactor
    (alpha : ℝ) (S : List CCM24VisiblePrime) :
    HasDerivAt (fun beta : ℝ => parameterizedFiniteEulerFactor beta S)
      (parameterizedFiniteEulerDerivative alpha S) alpha := by
  induction S with
  | nil =>
      simpa [parameterizedFiniteEulerFactor,
        parameterizedFiniteEulerDerivative] using
        (hasDerivAt_const alpha
          (1 : finiteSCarrier →L[ℂ] finiteSCarrier))
  | cons p S ih =>
      simpa only [parameterizedFiniteEulerFactor,
        parameterizedFiniteEulerDerivative] using
        (hasDerivAt_parameterizedPrimeEulerFactor alpha p).mul ih

/-- Concrete Banach-algebra unit carried by the synchronized product and its
reverse Neumann inverse. -/
noncomputable def parameterizedFiniteEulerUnit
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (finiteSCarrier →L[ℂ] finiteSCarrier)ˣ where
  val := parameterizedFiniteEulerFactor alpha S
  inv := parameterizedFiniteEulerInverse alpha S
  val_inv := parameterizedFiniteEulerFactor_mul_inverse alpha S halpha
  inv_val := parameterizedFiniteEulerInverse_mul_factor alpha S halpha

@[simp]
theorem parameterizedFiniteEulerUnit_val
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ((parameterizedFiniteEulerUnit alpha S halpha :
      (finiteSCarrier →L[ℂ] finiteSCarrier)ˣ) :
        finiteSCarrier →L[ℂ] finiteSCarrier) =
      parameterizedFiniteEulerFactor alpha S :=
  rfl

@[simp]
theorem parameterizedFiniteEulerUnit_inv_val
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (((parameterizedFiniteEulerUnit alpha S halpha)⁻¹ :
      (finiteSCarrier →L[ℂ] finiteSCarrier)ˣ) :
        finiteSCarrier →L[ℂ] finiteSCarrier) =
      parameterizedFiniteEulerInverse alpha S :=
  rfl

/-- The reverse Neumann product is the canonical ring inverse at every legal
synchronized time. -/
theorem ringInverse_parameterizedFiniteEulerFactor
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    Ring.inverse (parameterizedFiniteEulerFactor alpha S) =
      parameterizedFiniteEulerInverse alpha S := by
  change Ring.inverse
      ((parameterizedFiniteEulerUnit alpha S halpha :
        (finiteSCarrier →L[ℂ] finiteSCarrier)ˣ) :
          finiteSCarrier →L[ℂ] finiteSCarrier) =
    parameterizedFiniteEulerInverse alpha S
  rw [Ring.inverse_unit]
  rfl

end CCM24FiniteSParameterizedEulerCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
