/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionKernelCovariance
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite matrix owner of the support-first covariance

This module connects the two-point scalar to the literal finite matrix trace
`Tr(P W (I-P) H P)`.  It is a finite algebra theorem, not a replacement for
the continuous source trace-class producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMatrixCovariance

open scoped BigOperators ComplexConjugate Matrix
open CCM24FiniteSSupportFirstCovariance
open CCM24FiniteSProjectionKernelCovariance

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-- Literal finite matrix covariance. -/
noncomputable def matrixProjectionCovariance
    (projection : Matrix X X ℂ) (w h : X → ℂ) : ℂ :=
  Matrix.trace
    (projection * Matrix.diagonal w * (1 - projection) *
      Matrix.diagonal h * projection)

theorem trace_projection_diagonal_projection
    (projection : Matrix X X ℂ) (w h : X → ℂ)
    (hIdempotent : projection * projection = projection) :
    Matrix.trace
        (projection * Matrix.diagonal w * Matrix.diagonal h * projection) =
      ∑ x, w x * h x * projection x x := by
  let W := Matrix.diagonal w
  let H := Matrix.diagonal h
  calc
    Matrix.trace (projection * W * H * projection) =
        Matrix.trace (projection * (W * H) * projection) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (projection * projection * (W * H)) :=
      Matrix.trace_mul_cycle projection (W * H) projection
    _ = Matrix.trace (projection * (W * H)) := by rw [hIdempotent]
    _ = Matrix.trace ((W * H) * projection) :=
      Matrix.trace_mul_comm projection (W * H)
    _ = ∑ x, w x * h x * projection x x := by
      dsimp [W, H]
      rw [Matrix.diagonal_mul_diagonal]
      simp [Matrix.trace]

theorem trace_projection_diagonal_projection_diagonal_projection
    (projection : Matrix X X ℂ) (w h : X → ℂ)
    (hIdempotent : projection * projection = projection) :
    Matrix.trace
        (projection * Matrix.diagonal w * projection *
          Matrix.diagonal h * projection) =
      ∑ x, ∑ y,
        w x * projection x y * h y * projection y x := by
  let W := Matrix.diagonal w
  let H := Matrix.diagonal h
  have hWP (x y : X) :
      (W * projection) x y = w x * projection x y := by
    exact Matrix.diagonal_mul w projection x y
  have hWPH (x y : X) :
      (W * projection * H) x y =
        w x * projection x y * h y := by
    rw [Matrix.mul_diagonal, hWP]
  calc
    Matrix.trace (projection * W * projection * H * projection) =
        Matrix.trace (projection * (W * projection * H) * projection) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (projection * projection * (W * projection * H)) :=
      Matrix.trace_mul_cycle projection (W * projection * H) projection
    _ = Matrix.trace (projection * (W * projection * H)) := by
      rw [hIdempotent]
    _ = Matrix.trace ((W * projection * H) * projection) :=
      Matrix.trace_mul_comm projection (W * projection * H)
    _ = ∑ x, ∑ y,
        w x * projection x y * h y * projection y x := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [hWPH]

/-- The literal finite trace equals the expanded projection covariance. -/
theorem matrixProjectionCovariance_eq_expanded
    (projection : Matrix X X ℂ) (w h : X → ℂ)
    (hIdempotent : projection * projection = projection) :
    matrixProjectionCovariance projection w h =
      expandedProjectionCovariance projection w h := by
  unfold matrixProjectionCovariance expandedProjectionCovariance
  rw [show projection * Matrix.diagonal w * (1 - projection) *
      Matrix.diagonal h * projection =
      projection * Matrix.diagonal w * Matrix.diagonal h * projection -
        projection * Matrix.diagonal w * projection *
          Matrix.diagonal h * projection by noncomm_ring]
  rw [Matrix.trace_sub,
    trace_projection_diagonal_projection projection w h hIdempotent,
    trace_projection_diagonal_projection_diagonal_projection
      projection w h hIdempotent]

/-- A Hermitian idempotent matrix has the support-first symmetric two-point
trace formula. -/
theorem matrixProjectionCovariance_eq_symmetric
    (projection : Matrix X X ℂ) (w h : X → ℂ)
    (hIdempotent : projection * projection = projection)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    matrixProjectionCovariance projection w h =
      symmetricTwoPointCovariance
        (projectionKernelMass projection) w h := by
  rw [matrixProjectionCovariance_eq_expanded projection w h hIdempotent]
  apply expandedProjectionCovariance_eq_symmetric projection w h
  · intro x
    have hdiag := congrArg (fun matrix : Matrix X X ℂ => matrix x x)
      hIdempotent
    simpa only [Matrix.mul_apply] using hdiag.symm
  · exact hHermitian

/-- The compact root correlation is restricted before the finite matrix
projection modes are separated. -/
theorem matrixProjectionCovariance_correlation_support
    (projection : Matrix X X ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ) (h : X → ℂ)
    (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0)
    (hIdempotent : projection * projection = projection)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    matrixProjectionCovariance projection
        (correlationMultiplier correlation character) h =
      ∑ u ∈ support, correlation u *
        matrixProjectionCovariance projection (character u) h := by
  have hDiagonal : ∀ x, projection x x =
      ∑ y, projection x y * projection y x := by
    intro x
    have hdiag := congrArg (fun matrix : Matrix X X ℂ => matrix x x)
      hIdempotent
    simpa only [Matrix.mul_apply] using hdiag.symm
  calc
    matrixProjectionCovariance projection
        (correlationMultiplier correlation character) h =
        expandedProjectionCovariance projection
          (correlationMultiplier correlation character) h :=
      matrixProjectionCovariance_eq_expanded projection _ h hIdempotent
    _ = ∑ u ∈ support, correlation u *
          expandedProjectionCovariance projection (character u) h :=
      expandedProjectionCovariance_correlation_support projection
        correlation character h support hzero hDiagonal hHermitian
    _ = ∑ u ∈ support, correlation u *
          matrixProjectionCovariance projection (character u) h := by
      apply Finset.sum_congr rfl
      intro u _
      rw [matrixProjectionCovariance_eq_expanded projection
        (character u) h hIdempotent]

end CCM24FiniteSMatrixCovariance
end CCM25Concrete
end Source
end ConnesWeilRH
