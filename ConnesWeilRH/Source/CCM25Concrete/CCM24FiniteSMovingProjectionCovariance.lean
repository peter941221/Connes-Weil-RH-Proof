/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSynchronizedCovariance

/-!
# Moving finite projection covariance

This module identifies the literal first derivative of a moving orthogonal
projection with the support-first covariance.  The generator is diagonal in
the finite spectral model, exactly as for the CCM24 Euler multiplier.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingProjectionCovariance

open scoped BigOperators ComplexConjugate Matrix
open CCM24FiniteSMatrixCovariance
open CCM24FiniteSSynchronizedCovariance

variable {X U V : Type*} [Fintype X] [DecidableEq X]
  [Fintype U] [Fintype V]

/-- The derivative of the orthogonal projection onto a diagonally transported
range.  This is the finite-matrix form of
`P' = (I-P) X P + P X† (I-P)`. -/
noncomputable def diagonalProjectionDerivative
    (projection : Matrix X X ℂ) (generator : X → ℂ) : Matrix X X ℂ :=
  (1 - projection) * Matrix.diagonal generator * projection +
    projection * (Matrix.diagonal generator)ᴴ * (1 - projection)

/-- The detector trace of the moving projection derivative. -/
noncomputable def movingProjectionTraceResponse
    (projection : Matrix X X ℂ) (w generator : X → ℂ) : ℂ :=
  Matrix.trace
    (Matrix.diagonal w * diagonalProjectionDerivative projection generator)

omit [Fintype X] [DecidableEq X] in
theorem hermitian_matrix_eq_conjTranspose
    (projection : Matrix X X ℂ)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    projectionᴴ = projection := by
  ext x y
  exact (hHermitian y x).symm

omit [Fintype X] in
theorem real_diagonal_eq_conjTranspose
    (w : X → ℂ) (hReal : ∀ x, conj (w x) = w x) :
    (Matrix.diagonal w)ᴴ = Matrix.diagonal w := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  exact hReal x

theorem trace_diagonal_leftCrossing_eq_covariance
    (projection : Matrix X X ℂ) (w generator : X → ℂ)
    (hIdempotent : projection * projection = projection) :
    Matrix.trace
        (Matrix.diagonal w *
          ((1 - projection) * Matrix.diagonal generator * projection)) =
      matrixProjectionCovariance projection w generator := by
  let W := Matrix.diagonal w
  let H := Matrix.diagonal generator
  have hCovariance :
      matrixProjectionCovariance projection w generator =
        Matrix.trace (projection * W * (1 - projection) * H) := by
    unfold matrixProjectionCovariance
    calc
      Matrix.trace
          (projection * W * (1 - projection) * H * projection) =
          Matrix.trace
            (projection * projection * (W * (1 - projection) * H)) := by
        rw [show projection * W * (1 - projection) * H * projection =
            projection * (W * (1 - projection) * H) * projection by
          noncomm_ring]
        exact Matrix.trace_mul_cycle projection
          (W * (1 - projection) * H) projection
      _ = Matrix.trace (projection * W * (1 - projection) * H) := by
        rw [hIdempotent]
        congr 1
        noncomm_ring
  calc
    Matrix.trace
        (Matrix.diagonal w *
          ((1 - projection) * Matrix.diagonal generator * projection)) =
        Matrix.trace
          (W * (((1 - projection) * H) * projection)) := by rfl
    _ = Matrix.trace (projection * (W * ((1 - projection) * H))) := by
      exact Matrix.trace_mul_cycle' W ((1 - projection) * H) projection
    _ = Matrix.trace (projection * W * (1 - projection) * H) := by
      congr 1
      noncomm_ring
    _ = matrixProjectionCovariance projection w generator :=
      hCovariance.symm

theorem trace_diagonal_rightCrossing_eq_conj_covariance
    (projection : Matrix X X ℂ) (w generator : X → ℂ)
    (hIdempotent : projection * projection = projection)
    (hHermitian : ∀ x y, projection y x = conj (projection x y))
    (hReal : ∀ x, conj (w x) = w x) :
    Matrix.trace
        (Matrix.diagonal w *
          (projection * (Matrix.diagonal generator)ᴴ * (1 - projection))) =
      conj (matrixProjectionCovariance projection w generator) := by
  let W := Matrix.diagonal w
  let H := Matrix.diagonal generator
  have hP : projectionᴴ = projection :=
    hermitian_matrix_eq_conjTranspose projection hHermitian
  have hW : Wᴴ = W := real_diagonal_eq_conjTranspose w hReal
  have hC : (1 - projection)ᴴ = 1 - projection := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP]
  have hLeft := trace_diagonal_leftCrossing_eq_covariance
    projection w generator hIdempotent
  calc
    Matrix.trace
        (Matrix.diagonal w *
          (projection * (Matrix.diagonal generator)ᴴ * (1 - projection))) =
        Matrix.trace ((projection * Hᴴ * (1 - projection)) * W) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace
        ((W * ((1 - projection) * H * projection))ᴴ) := by
      congr 1
      simp only [Matrix.conjTranspose_mul, hP, hW, hC]
      noncomm_ring
    _ = conj
        (Matrix.trace (W * ((1 - projection) * H * projection))) := by
      rw [Matrix.trace_conjTranspose, Complex.star_def]
    _ = conj (matrixProjectionCovariance projection w generator) := by
      rw [hLeft]

/-- The literal moving trace is twice the real part of the oriented crossing
covariance. -/
theorem movingProjectionTraceResponse_eq_two_re
    (projection : Matrix X X ℂ) (w generator : X → ℂ)
    (hIdempotent : projection * projection = projection)
    (hHermitian : ∀ x y, projection y x = conj (projection x y))
    (hReal : ∀ x, conj (w x) = w x) :
    movingProjectionTraceResponse projection w generator =
      (2 * (matrixProjectionCovariance projection w generator).re : ℝ) := by
  unfold movingProjectionTraceResponse diagonalProjectionDerivative
  rw [Matrix.mul_add, Matrix.trace_add,
    trace_diagonal_leftCrossing_eq_covariance projection w generator
      hIdempotent,
    trace_diagonal_rightCrossing_eq_conj_covariance projection w generator
      hIdempotent hHermitian hReal,
    Complex.add_conj]

/-- The moving outer-minus-Sonin response. -/
noncomputable def signedMovingProjectionTraceResponse
    (outerProjection soninProjection : Matrix X X ℂ)
    (w generator : X → ℂ) : ℂ :=
  movingProjectionTraceResponse outerProjection w generator -
    movingProjectionTraceResponse soninProjection w generator

/-- The signed moving trace is the real part of one complete nested
covariance. -/
theorem signedMovingProjectionTraceResponse_eq_two_re
    (outerProjection soninProjection : Matrix X X ℂ)
    (w generator : X → ℂ)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y))
    (hReal : ∀ x, conj (w x) = w x) :
    signedMovingProjectionTraceResponse outerProjection soninProjection
        w generator =
      (2 * Complex.re (signedMatrixProjectionCovariance
        outerProjection soninProjection w generator) : ℝ) := by
  unfold signedMovingProjectionTraceResponse
    signedMatrixProjectionCovariance
  rw [movingProjectionTraceResponse_eq_two_re outerProjection w generator
      hOuterIdempotent hOuterHermitian hReal,
    movingProjectionTraceResponse_eq_two_re soninProjection w generator
      hSoninIdempotent hSoninHermitian hReal]
  norm_cast
  rw [Complex.sub_re]
  ring

/-- The actual moving response keeps the complete generator inside the signed
outer-minus-Sonin owner. -/
theorem signedMovingProjectionTraceResponse_completeGenerator
    (outerProjection soninProjection : Matrix X X ℂ)
    (w : X → ℂ) (channel : V → X → ℂ)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y))
    (hReal : ∀ x, conj (w x) = w x) :
    signedMovingProjectionTraceResponse outerProjection soninProjection w
        (completeGenerator channel) =
      (2 * Complex.re (∑ v, signedMatrixProjectionCovariance
        outerProjection soninProjection w (channel v)) : ℝ) := by
  rw [signedMovingProjectionTraceResponse_eq_two_re outerProjection
      soninProjection w _ hOuterIdempotent hSoninIdempotent
      hOuterHermitian hSoninHermitian hReal,
    signedMatrixProjectionCovariance_completeGenerator outerProjection
      soninProjection w channel hOuterIdempotent hSoninIdempotent
      hOuterHermitian hSoninHermitian]

end CCM24FiniteSMovingProjectionCovariance
end CCM25Concrete
end Source
end ConnesWeilRH
