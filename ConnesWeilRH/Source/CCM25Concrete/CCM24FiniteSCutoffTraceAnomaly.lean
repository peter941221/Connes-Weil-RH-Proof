/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-cutoff trace-anomaly guard

This module records the finite matrix obstruction behind a common
fixed-particle-number cutoff.  A translation-invariant detector has constant
diagonal, so equal-cardinality coordinate windows have exactly equal detector
trace.  Retaining a nonzero boundary response requires a cardinality defect.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCutoffTraceAnomaly

open scoped BigOperators Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The orthogonal coordinate projection onto a finite set of basis labels. -/
noncomputable def coordinateProjection (support : Finset X) : Matrix X X ℂ :=
  Matrix.diagonal fun x => if x ∈ support then 1 else 0

/-- A matrix trace against a coordinate projection reads only the selected
diagonal entries. -/
theorem trace_mul_coordinateProjection_eq_sum
    (detector : Matrix X X ℂ) (support : Finset X) :
    Matrix.trace (detector * coordinateProjection support) =
      ∑ x ∈ support, detector x x := by
  simp [coordinateProjection, Matrix.trace, Matrix.mul_diagonal]

/-- A detector with constant basis diagonal charges a coordinate window only
by its cardinality. -/
theorem trace_mul_coordinateProjection_eq_card_mul
    (detector : Matrix X X ℂ) (support : Finset X) (diagonalValue : ℂ)
    (hdiagonal : ∀ x, detector x x = diagonalValue) :
    Matrix.trace (detector * coordinateProjection support) =
      (support.card : ℂ) * diagonalValue := by
  rw [trace_mul_coordinateProjection_eq_sum]
  calc
    (∑ x ∈ support, detector x x) = ∑ _x ∈ support, diagonalValue := by
      apply Finset.sum_congr rfl
      intro x _
      exact hdiagonal x
    _ = (support.card : ℂ) * diagonalValue := by simp

/-- The finite relative response is exactly the coordinate-rank defect times
the constant detector diagonal. -/
theorem coordinateProjection_response_eq_card_sub_mul
    (detector : Matrix X X ℂ) (source target : Finset X)
    (diagonalValue : ℂ)
    (hdiagonal : ∀ x, detector x x = diagonalValue) :
    Matrix.trace (detector * coordinateProjection source) -
        Matrix.trace (detector * coordinateProjection target) =
      ((source.card : ℂ) - (target.card : ℂ)) * diagonalValue := by
  rw [trace_mul_coordinateProjection_eq_card_mul detector source
      diagonalValue hdiagonal,
    trace_mul_coordinateProjection_eq_card_mul detector target
      diagonalValue hdiagonal]
  ring

/-- Equal-cardinality cutoffs erase the boundary response exactly. -/
theorem equalCard_coordinateProjection_response_eq_zero
    (detector : Matrix X X ℂ) (source target : Finset X)
    (diagonalValue : ℂ)
    (hdiagonal : ∀ x, detector x x = diagonalValue)
    (hcard : source.card = target.card) :
    Matrix.trace (detector * coordinateProjection source) -
        Matrix.trace (detector * coordinateProjection target) = 0 := by
  rw [coordinateProjection_response_eq_card_sub_mul detector source target
    diagonalValue hdiagonal, hcard, sub_self, zero_mul]

/-- The same cancellation written as one relative matrix trace. -/
theorem trace_mul_coordinateProjection_sub_eq_zero
    (detector : Matrix X X ℂ) (source target : Finset X)
    (diagonalValue : ℂ)
    (hdiagonal : ∀ x, detector x x = diagonalValue)
    (hcard : source.card = target.card) :
    Matrix.trace
        (detector *
          (coordinateProjection source - coordinateProjection target)) = 0 := by
  rw [mul_sub, Matrix.trace_sub]
  exact equalCard_coordinateProjection_response_eq_zero detector source target
    diagonalValue hdiagonal hcard

/-- Finite trace cyclicity erases every similarity response whose transport
commutes with the detector.  The unitary gauge case is the detector-diagonal
form of the translated equal-rank cutoff. -/
theorem trace_commuting_similarity_eq
    (detector projection transport inverse : Matrix X X ℂ)
    (hinverse : inverse * transport = 1)
    (hcommute : detector * transport = transport * detector) :
    Matrix.trace
        (detector * (transport * projection * inverse)) =
      Matrix.trace (detector * projection) := by
  calc
    Matrix.trace (detector * (transport * projection * inverse)) =
        Matrix.trace ((detector * transport * projection) * inverse) := by
      congr 1
      simp only [mul_assoc]
    _ = Matrix.trace (inverse * (detector * transport * projection)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((inverse * transport) * (detector * projection)) := by
      congr 1
      rw [hcommute]
      simp only [mul_assoc]
    _ = Matrix.trace (detector * projection) := by rw [hinverse, one_mul]

end CCM24FiniteSCutoffTraceAnomaly
end CCM25Concrete
end Source
end ConnesWeilRH
