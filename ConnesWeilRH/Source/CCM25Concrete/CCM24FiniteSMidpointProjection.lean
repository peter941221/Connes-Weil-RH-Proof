/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Group.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# Canonical-midpoint projection algebra

This module owns the unconditional algebra behind Proof 354.  The difference
and bisector of two idempotents anticommute and have complementary squares.
Once a midpoint projection has zero diagonal compression of the difference,
the difference is exactly the sum of its two midpoint crossing corners.

The analytic construction of the canonical midpoint and its uniform
root-sandwiched Schatten estimates are intentionally not stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMidpointProjection

variable {A : Type*} [Ring A]

/-- Difference of two candidate orthogonal range projections. -/
def projectionDifference (P0 P1 : A) : A :=
  P1 - P0

/-- Bisector operator of two candidate orthogonal range projections. -/
def projectionBisector (P0 P1 : A) : A :=
  P1 + P0 - 1

/-- The projection difference anticommutes with the bisector. -/
theorem projectionDifference_anticommutes_projectionBisector
    (P0 P1 : A) (hP0 : IsIdempotentElem P0)
    (hP1 : IsIdempotentElem P1) :
    projectionDifference P0 P1 * projectionBisector P0 P1 +
        projectionBisector P0 P1 * projectionDifference P0 P1 = 0 := by
  have hP0sq : P0 * P0 = P0 := hP0
  have hP1sq : P1 * P1 = P1 := hP1
  unfold projectionDifference projectionBisector
  calc
    (P1 - P0) * (P1 + P0 - 1) +
        (P1 + P0 - 1) * (P1 - P0) =
      2 * (P1 * P1) - 2 * (P0 * P0) - 2 * P1 + 2 * P0 := by
        noncomm_ring
    _ = 0 := by rw [hP0sq, hP1sq]; noncomm_ring

/-- The squared difference and squared bisector sum to the identity. -/
theorem projectionDifference_sq_add_projectionBisector_sq
    (P0 P1 : A) (hP0 : IsIdempotentElem P0)
    (hP1 : IsIdempotentElem P1) :
    projectionDifference P0 P1 * projectionDifference P0 P1 +
        projectionBisector P0 P1 * projectionBisector P0 P1 = 1 := by
  have hP0sq : P0 * P0 = P0 := hP0
  have hP1sq : P1 * P1 = P1 := hP1
  unfold projectionDifference projectionBisector
  calc
    (P1 - P0) * (P1 - P0) +
        (P1 + P0 - 1) * (P1 + P0 - 1) =
      2 * (P1 * P1) + 2 * (P0 * P0) - 2 * P1 - 2 * P0 + 1 := by
        noncomm_ring
    _ = 1 := by rw [hP0sq, hP1sq]; noncomm_ring

/-- Oriented off-diagonal corner of a projection difference relative to a
midpoint projection. -/
def midpointDifferenceCorner (M P0 P1 : A) : A :=
  (1 - M) * projectionDifference P0 P1 * M

/-- If both midpoint diagonal compressions vanish, the complete projection
difference is the sum of its two oriented midpoint corners. -/
theorem projectionDifference_eq_midpointDifferenceCorners
    (M P0 P1 : A) (hM : IsIdempotentElem M)
    (hdiag : M * projectionDifference P0 P1 * M = 0)
    (hdiagComplement :
      (1 - M) * projectionDifference P0 P1 * (1 - M) = 0) :
    projectionDifference P0 P1 =
      midpointDifferenceCorner M P0 P1 +
        M * projectionDifference P0 P1 * (1 - M) := by
  have hM_sq : M * M = M := hM
  unfold midpointDifferenceCorner
  calc
    projectionDifference P0 P1 =
        (M + (1 - M)) * projectionDifference P0 P1 *
          (M + (1 - M)) := by noncomm_ring
    _ = M * projectionDifference P0 P1 * M +
          M * projectionDifference P0 P1 * (1 - M) +
          (1 - M) * projectionDifference P0 P1 * M +
          (1 - M) * projectionDifference P0 P1 * (1 - M) := by
        noncomm_ring
    _ = (1 - M) * projectionDifference P0 P1 * M +
          M * projectionDifference P0 P1 * (1 - M) := by
        rw [hdiag, hdiagComplement]
        noncomm_ring

end CCM24FiniteSMidpointProjection
end CCM25Concrete
end Source
end ConnesWeilRH
