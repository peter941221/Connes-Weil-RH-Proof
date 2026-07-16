/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSObliqueProjectionCalculus

/-!
# Orthogonal projection flow algebra on the common-log carrier

This module lifts the moving-projection algebra from finite matrices to the
actual Hilbert-space operator algebra.  It isolates the exact off-diagonal
derivative that the Gram-corrected moving Sonin projection must realize.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSOrthogonalProjectionFlow

open CC20Concrete
open CCM24FiniteSProjectionTrace

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The oriented crossing of a projection by a generator. -/
noncomputable def projectionLeftCrossing (P X : Op) : Op :=
  (1 - P) * X * P

/-- Canonical self-adjoint tangent to the orthogonal Grassmannian. -/
noncomputable def orthogonalProjectionDerivative (P X : Op) : Op :=
  projectionLeftCrossing P X +
    ContinuousLinearMap.adjoint (projectionLeftCrossing P X)

theorem adjoint_projectionLeftCrossing (P X : Op)
    (hP : IsSelfAdjoint P) :
    ContinuousLinearMap.adjoint (projectionLeftCrossing P X) =
      P * ContinuousLinearMap.adjoint X * (1 - P) := by
  unfold projectionLeftCrossing
  change star ((1 - P) * X * P) = P * star X * (1 - P)
  simp only [star_mul, star_sub, star_one, hP.star_eq]
  exact (mul_assoc _ _ _).symm

/-- Explicit two-crossing form used by the support-first trace owner. -/
theorem orthogonalProjectionDerivative_eq_twoCrossings
    (P X : Op) (hP : IsSelfAdjoint P) :
    orthogonalProjectionDerivative P X =
      (1 - P) * X * P +
        P * ContinuousLinearMap.adjoint X * (1 - P) := by
  rw [orthogonalProjectionDerivative,
    adjoint_projectionLeftCrossing P X hP]
  rfl

/-- The expanded Gram derivative collapses to the same off-diagonal
expression before any norm is taken. -/
theorem expandedGramDerivative_eq_orthogonalProjectionDerivative
    (P X : Op) (hP : IsSelfAdjoint P) :
    X * P + P * ContinuousLinearMap.adjoint X -
        P * X * P - P * ContinuousLinearMap.adjoint X * P =
      orthogonalProjectionDerivative P X := by
  rw [orthogonalProjectionDerivative_eq_twoCrossings P X hP]
  noncomm_ring

theorem orthogonalProjectionDerivative_isSelfAdjoint
    (P X : Op) :
    IsSelfAdjoint (orthogonalProjectionDerivative P X) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold orthogonalProjectionDerivative
  simp only [map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]

/-- A projection tangent has no diagonal `P/P` block. -/
theorem projection_compress_orthogonalProjectionDerivative_eq_zero
    (P X : Op) (hP : IsIdempotentElem P)
    (hself : IsSelfAdjoint P) :
    P * orthogonalProjectionDerivative P X * P = 0 := by
  rw [orthogonalProjectionDerivative_eq_twoCrossings P X hself]
  have hPP : P * P = P := hP
  have hPcomp : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hPP, sub_self]
  have hcompP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hPP, sub_self]
  calc
    P * ((1 - P) * X * P +
          P * ContinuousLinearMap.adjoint X * (1 - P)) * P =
        (P * (1 - P)) * X * P * P +
          P * P * ContinuousLinearMap.adjoint X * ((1 - P) * P) := by
      noncomm_ring
    _ = 0 := by rw [hPcomp, hcompP]; simp

/-- The complementary diagonal block also vanishes. -/
theorem complement_compress_orthogonalProjectionDerivative_eq_zero
    (P X : Op) (hP : IsIdempotentElem P)
    (hself : IsSelfAdjoint P) :
    (1 - P) * orthogonalProjectionDerivative P X * (1 - P) = 0 := by
  rw [orthogonalProjectionDerivative_eq_twoCrossings P X hself]
  have hPP : P * P = P := hP
  have hPcomp : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hPP, sub_self]
  have hcompP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hPP, sub_self]
  calc
    (1 - P) * ((1 - P) * X * P +
          P * ContinuousLinearMap.adjoint X * (1 - P)) * (1 - P) =
        (1 - P) * (1 - P) * X * (P * (1 - P)) +
          ((1 - P) * P) * ContinuousLinearMap.adjoint X *
            (1 - P) * (1 - P) := by
      noncomm_ring
    _ = 0 := by rw [hPcomp, hcompP]; simp

end CCM24FiniteSOrthogonalProjectionFlow
end CCM25Concrete
end Source
end ConnesWeilRH
