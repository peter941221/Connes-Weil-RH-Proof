/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSAdjointCalculus

/-!
# Oblique projection calculus for the moving Sonin range

The similarity `T P T⁻¹` is used only as a differentiable range ledger.  It
is not used as the orthogonal Sonin projection.  Its derivative is the exact
commutator with the complete same-object Euler generator.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSObliqueProjectionCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerCommutation
open CCM24FiniteSParameterizedEulerCalculus
open CCM24FiniteSParameterizedInverseCalculus

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The fixed source complete-Sonin orthogonal projection. -/
noncomputable def sourceSoninStarProjection (lambda : CCM24SoninScale) : Op :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.starProjection

/-- Oblique similarity with the correct moving Sonin range.  This is not the
canonical target orthogonal projection. -/
noncomputable def parameterizedObliqueSoninProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  parameterizedFiniteEulerFactor alpha S *
    sourceSoninStarProjection lambda *
    parameterizedFiniteEulerInverse alpha S

/-- Product-rule derivative before the commutator collapse. -/
noncomputable def parameterizedObliqueSoninProjectionDerivative
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  parameterizedFiniteEulerDerivative alpha S *
      sourceSoninStarProjection lambda *
      parameterizedFiniteEulerInverse alpha S +
    parameterizedFiniteEulerFactor alpha S *
      sourceSoninStarProjection lambda *
      parameterizedFiniteEulerInverseDerivative alpha S

/-- The oblique range ledger is norm differentiable at every interior
synchronized time. -/
theorem hasDerivAt_parameterizedObliqueSoninProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| < 1) :
    HasDerivAt
      (fun beta : ℝ =>
        parameterizedObliqueSoninProjection lambda beta S)
      (parameterizedObliqueSoninProjectionDerivative lambda alpha S)
      alpha := by
  have hsource : HasDerivAt
      (fun _ : ℝ => sourceSoninStarProjection lambda) 0 alpha :=
    hasDerivAt_const alpha _
  have hleft :=
    (hasDerivAt_parameterizedFiniteEulerFactor alpha S).mul hsource
  have hall := hleft.mul
    (hasDerivAt_parameterizedFiniteEulerInverse alpha S halpha)
  simpa only [parameterizedObliqueSoninProjection,
    parameterizedObliqueSoninProjectionDerivative, zero_mul, add_zero,
    mul_zero] using hall

/-- The derivative is the exact commutator `[X_S,Q_alpha]` with the complete
additive prime-power generator. -/
theorem parameterizedObliqueSoninProjectionDerivative_eq_commutator
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedObliqueSoninProjectionDerivative lambda alpha S =
      parameterizedFiniteEulerGenerator alpha S *
          parameterizedObliqueSoninProjection lambda alpha S -
        parameterizedObliqueSoninProjection lambda alpha S *
          parameterizedFiniteEulerGenerator alpha S := by
  have hXT := parameterizedFiniteEulerGenerator_mul_factor
    alpha S halpha
  have hDX : parameterizedFiniteEulerDerivative alpha S *
      parameterizedFiniteEulerInverse alpha S =
      parameterizedFiniteEulerGenerator alpha S := by
    exact parameterizedFiniteEulerRightGenerator_eq_additiveGenerator
      alpha S halpha
  unfold parameterizedObliqueSoninProjectionDerivative
    parameterizedObliqueSoninProjection
    parameterizedFiniteEulerInverseDerivative
  calc
    parameterizedFiniteEulerDerivative alpha S *
          sourceSoninStarProjection lambda *
          parameterizedFiniteEulerInverse alpha S +
        parameterizedFiniteEulerFactor alpha S *
          sourceSoninStarProjection lambda *
          (-(parameterizedFiniteEulerInverse alpha S *
            parameterizedFiniteEulerDerivative alpha S *
            parameterizedFiniteEulerInverse alpha S)) =
        parameterizedFiniteEulerDerivative alpha S *
            sourceSoninStarProjection lambda *
            parameterizedFiniteEulerInverse alpha S -
          parameterizedFiniteEulerFactor alpha S *
            sourceSoninStarProjection lambda *
            parameterizedFiniteEulerInverse alpha S *
            parameterizedFiniteEulerDerivative alpha S *
            parameterizedFiniteEulerInverse alpha S := by
      noncomm_ring
    _ = (parameterizedFiniteEulerGenerator alpha S *
            parameterizedFiniteEulerFactor alpha S) *
            sourceSoninStarProjection lambda *
            parameterizedFiniteEulerInverse alpha S -
          parameterizedFiniteEulerFactor alpha S *
            sourceSoninStarProjection lambda *
            parameterizedFiniteEulerInverse alpha S *
            (parameterizedFiniteEulerDerivative alpha S *
              parameterizedFiniteEulerInverse alpha S) := by
      rw [hXT]
      noncomm_ring
    _ = parameterizedFiniteEulerGenerator alpha S *
          (parameterizedFiniteEulerFactor alpha S *
            sourceSoninStarProjection lambda *
            parameterizedFiniteEulerInverse alpha S) -
        (parameterizedFiniteEulerFactor alpha S *
          sourceSoninStarProjection lambda *
          parameterizedFiniteEulerInverse alpha S) *
          parameterizedFiniteEulerGenerator alpha S := by
      rw [hDX]
      noncomm_ring

/-- Direct differentiable commutator form. -/
theorem hasDerivAt_parameterizedObliqueSoninProjection_commutator
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| < 1) :
    HasDerivAt
      (fun beta : ℝ =>
        parameterizedObliqueSoninProjection lambda beta S)
      (parameterizedFiniteEulerGenerator alpha S *
          parameterizedObliqueSoninProjection lambda alpha S -
        parameterizedObliqueSoninProjection lambda alpha S *
          parameterizedFiniteEulerGenerator alpha S)
      alpha := by
  rw [← parameterizedObliqueSoninProjectionDerivative_eq_commutator
    lambda alpha S halpha.le]
  exact hasDerivAt_parameterizedObliqueSoninProjection
    lambda alpha S halpha

end CCM24FiniteSObliqueProjectionCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
