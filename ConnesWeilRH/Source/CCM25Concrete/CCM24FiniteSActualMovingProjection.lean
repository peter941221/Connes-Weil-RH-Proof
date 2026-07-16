/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramFlowCollapse

/-!
# Actual moving finite-S Sonin projection

This module packages the proof-independent Gram path as the actual moving
orthogonal Sonin projection on every legal synchronized time slice.  Its
operator-norm derivative is the completed two-crossing flow, and its endpoint
is the existing finite-S semilocal Sonin projection.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualMovingProjection

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSGramFlowCollapse
open CCM24FiniteSOrthogonalProjectionFlow

/-- On every legal time slice, the proof-independent Gram owner is the
canonical orthogonal projection onto the actual moving Sonin intersection. -/
theorem parameterizedCanonicalGramProjection_isStarProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsStarProjection
      (parameterizedCanonicalGramProjection lambda alpha S) := by
  rw [parameterizedCanonicalGramProjection_eq_soninProjection
    lambda alpha S halpha]
  exact parameterizedSoninProjection_isStarProjection
    lambda alpha S halpha

/-- The actual infinite-dimensional moving Sonin projection has the completed
orthogonal two-crossing derivative in operator norm. -/
theorem hasDerivAt_parameterizedCanonicalGramProjection_orthogonalFlow
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ =>
        parameterizedCanonicalGramProjection lambda beta S)
      (orthogonalProjectionDerivative
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S)) alpha := by
  rw [← parameterizedCanonicalGramProjectionDerivative_eq_orthogonalFlow
    lambda alpha S halpha]
  exact hasDerivAt_parameterizedCanonicalGramProjection
    lambda alpha S halpha

/-- Read the derivative directly in the actual Sonin projection at the
selected time slice, while retaining the proof-independent path. -/
theorem hasDerivAt_parameterizedCanonicalGramProjection_soninReadback
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ =>
        parameterizedCanonicalGramProjection lambda beta S)
      (orthogonalProjectionDerivative
        (parameterizedSoninProjection lambda alpha S halpha)
        (parameterizedFiniteEulerGenerator alpha S)) alpha := by
  rw [← parameterizedCanonicalGramProjection_eq_soninProjection
    lambda alpha S halpha]
  exact hasDerivAt_parameterizedCanonicalGramProjection_orthogonalFlow
    lambda alpha S halpha

/-- The proof-independent moving owner lands at the repository's existing
finite-S semilocal Sonin projection. -/
theorem parameterizedCanonicalGramProjection_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedCanonicalGramProjection lambda 1 S =
      (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule.starProjection := by
  rw [parameterizedCanonicalGramProjection_eq_soninProjection
      lambda 1 S (by norm_num),
    parameterizedSoninProjection_one]

/-- The tangent has no diagonal block inside the actual moving Sonin range. -/
theorem sonin_compress_parameterizedDerivative_eq_zero
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    let P := parameterizedCanonicalGramProjection lambda alpha S
    P * orthogonalProjectionDerivative P
        (parameterizedFiniteEulerGenerator alpha S) * P = 0 := by
  dsimp only
  exact projection_compress_orthogonalProjectionDerivative_eq_zero _ _
    (parameterizedCanonicalGramProjection_isStarProjection
      lambda alpha S halpha).isIdempotentElem
    (parameterizedCanonicalGramProjection_isStarProjection
      lambda alpha S halpha).isSelfAdjoint

/-- The tangent also has no diagonal block in the orthogonal complement. -/
theorem soninComplement_compress_parameterizedDerivative_eq_zero
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    let P := parameterizedCanonicalGramProjection lambda alpha S
    (1 - P) * orthogonalProjectionDerivative P
        (parameterizedFiniteEulerGenerator alpha S) * (1 - P) = 0 := by
  dsimp only
  exact complement_compress_orthogonalProjectionDerivative_eq_zero _ _
    (parameterizedCanonicalGramProjection_isStarProjection
      lambda alpha S halpha).isIdempotentElem
    (parameterizedCanonicalGramProjection_isStarProjection
      lambda alpha S halpha).isSelfAdjoint

end CCM24FiniteSActualMovingProjection
end CCM25Concrete
end Source
end ConnesWeilRH
