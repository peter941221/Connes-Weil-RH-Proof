/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSupportFirstCovariance

/-!
# Projection-kernel covariance readback

This module identifies the expanded finite projection covariance with the
support-first two-point kernel.  The projection diagonal is eliminated by
idempotence and Hermitian symmetry turns the remaining matrix product into
the symmetric kernel mass.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSProjectionKernelCovariance

open scoped BigOperators ComplexConjugate
open CCM24FiniteSSupportFirstCovariance

variable {X U : Type*} [Fintype X] [Fintype U]

/-- Scalar expansion of `Tr(P W (I-P) H P)` after finite cyclicity has placed
the diagonal multipliers outside the projection kernels. -/
noncomputable def expandedProjectionCovariance
    (projection : X → X → ℂ) (w h : X → ℂ) : ℂ :=
  (∑ x, w x * h x * projection x x) -
    ∑ x, ∑ y, w x * projection x y * h y * projection y x

/-- Idempotence on the diagonal and Hermitian symmetry identify the expanded
projection covariance with the oriented two-point covariance. -/
theorem expandedProjectionCovariance_eq_twoPoint
    (projection : X → X → ℂ) (w h : X → ℂ)
    (hDiagonal : ∀ x, projection x x =
      ∑ y, projection x y * projection y x)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    expandedProjectionCovariance projection w h =
      twoPointCovariance (projectionKernelMass projection) w h := by
  classical
  have hfirst :
      (∑ x, w x * h x * projection x x) =
        ∑ x, ∑ y,
          w x * h x * (projection x y * projection y x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hDiagonal x, Finset.mul_sum]
  unfold expandedProjectionCovariance twoPointCovariance
  rw [hfirst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [hHermitian x y]
  unfold projectionKernelMass
  ring

/-- The same scalar has the symmetric two-finite-difference form. -/
theorem expandedProjectionCovariance_eq_symmetric
    (projection : X → X → ℂ) (w h : X → ℂ)
    (hDiagonal : ∀ x, projection x x =
      ∑ y, projection x y * projection y x)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    expandedProjectionCovariance projection w h =
      symmetricTwoPointCovariance
        (projectionKernelMass projection) w h := by
  rw [expandedProjectionCovariance_eq_twoPoint projection w h
    hDiagonal hHermitian]
  exact projectionKernelCovariance_eq_symmetric projection w h hHermitian

/-- Cross-correlation support is applied directly to the projection trace
scalar, before a modewise absolute value. -/
theorem expandedProjectionCovariance_correlation_support
    (projection : X → X → ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ) (h : X → ℂ)
    (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0)
    (hDiagonal : ∀ x, projection x x =
      ∑ y, projection x y * projection y x)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    expandedProjectionCovariance projection
        (correlationMultiplier correlation character) h =
      ∑ u ∈ support, correlation u *
        expandedProjectionCovariance projection (character u) h := by
  rw [expandedProjectionCovariance_eq_twoPoint projection _ h
      hDiagonal hHermitian,
    twoPointCovariance_correlation_support
      (projectionKernelMass projection) correlation character h support hzero]
  apply Finset.sum_congr rfl
  intro u _
  rw [expandedProjectionCovariance_eq_twoPoint projection (character u) h
    hDiagonal hHermitian]

/-- The nested outer-minus-Sonin trace keeps both projection kernels inside
one support-restricted sum. -/
theorem signedExpandedProjectionCovariance_correlation_support
    (outerProjection soninProjection : X → X → ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ) (h : X → ℂ)
    (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0)
    (hOuterDiagonal : ∀ x, outerProjection x x =
      ∑ y, outerProjection x y * outerProjection y x)
    (hSoninDiagonal : ∀ x, soninProjection x x =
      ∑ y, soninProjection x y * soninProjection y x)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y)) :
    expandedProjectionCovariance outerProjection
        (correlationMultiplier correlation character) h -
      expandedProjectionCovariance soninProjection
        (correlationMultiplier correlation character) h =
      ∑ u ∈ support, correlation u *
        (expandedProjectionCovariance outerProjection (character u) h -
          expandedProjectionCovariance soninProjection (character u) h) := by
  rw [expandedProjectionCovariance_correlation_support outerProjection
      correlation character h support hzero hOuterDiagonal hOuterHermitian,
    expandedProjectionCovariance_correlation_support soninProjection
      correlation character h support hzero hSoninDiagonal hSoninHermitian,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

end CCM24FiniteSProjectionKernelCovariance
end CCM25Concrete
end Source
end ConnesWeilRH
