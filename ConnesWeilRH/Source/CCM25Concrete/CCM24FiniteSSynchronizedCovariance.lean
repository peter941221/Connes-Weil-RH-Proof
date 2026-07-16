/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMatrixCovariance

/-!
# Support-first synchronized generator covariance

The complete generator remains inside the same moving outer-minus-Sonin
kernel.  Compact root support is applied first; channel linearity is used only
after that restriction and does not authorize a channelwise absolute value.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSynchronizedCovariance

open scoped BigOperators ComplexConjugate Matrix
open CCM24FiniteSSupportFirstCovariance
open CCM24FiniteSProjectionKernelCovariance
open CCM24FiniteSMatrixCovariance

variable {X U V : Type*} [Fintype X] [DecidableEq X]
  [Fintype U] [Fintype V]

omit [DecidableEq X] in
theorem twoPointCovariance_add_right
    (mass : X → X → ℂ) (w h₁ h₂ : X → ℂ) :
    twoPointCovariance mass w (h₁ + h₂) =
      twoPointCovariance mass w h₁ +
        twoPointCovariance mass w h₂ := by
  classical
  unfold twoPointCovariance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Pi.add_apply]
  ring

omit [DecidableEq X] in
theorem twoPointCovariance_zero_right
    (mass : X → X → ℂ) (w : X → ℂ) :
    twoPointCovariance mass w 0 = 0 := by
  classical
  simp [twoPointCovariance]

omit [DecidableEq X] [Fintype V] in
theorem twoPointCovariance_finset_sum_right
    (mass : X → X → ℂ) (w : X → ℂ)
    (channel : V → X → ℂ) (channels : Finset V) :
    twoPointCovariance mass w
        (fun x => ∑ v ∈ channels, channel v x) =
      ∑ v ∈ channels, twoPointCovariance mass w (channel v) := by
  classical
  induction channels using Finset.induction_on with
  | empty =>
      simpa using twoPointCovariance_zero_right mass w
  | @insert v channels hv ih =>
      simp only [Finset.sum_insert hv]
      change twoPointCovariance mass w
          (channel v + fun x => ∑ a ∈ channels, channel a x) = _
      rw [twoPointCovariance_add_right, ih]

/-- Complete synchronized generator. -/
noncomputable def completeGenerator
    (channel : V → X → ℂ) (x : X) : ℂ :=
  ∑ v, channel v x

omit [DecidableEq X] in
theorem twoPointCovariance_completeGenerator
    (mass : X → X → ℂ) (w : X → ℂ)
    (channel : V → X → ℂ) :
    twoPointCovariance mass w (completeGenerator channel) =
      ∑ v, twoPointCovariance mass w (channel v) := by
  exact twoPointCovariance_finset_sum_right mass w channel Finset.univ

theorem matrixProjectionCovariance_eq_twoPoint
    (projection : Matrix X X ℂ) (w h : X → ℂ)
    (hIdempotent : projection * projection = projection)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    matrixProjectionCovariance projection w h =
      twoPointCovariance (projectionKernelMass projection) w h := by
  rw [matrixProjectionCovariance_eq_expanded projection w h hIdempotent]
  apply expandedProjectionCovariance_eq_twoPoint projection w h
  · intro x
    have hdiag := congrArg (fun matrix : Matrix X X ℂ => matrix x x)
      hIdempotent
    simpa only [Matrix.mul_apply] using hdiag.symm
  · exact hHermitian

/-- Channel linearity for the literal finite projection trace. -/
theorem matrixProjectionCovariance_completeGenerator
    (projection : Matrix X X ℂ) (w : X → ℂ)
    (channel : V → X → ℂ)
    (hIdempotent : projection * projection = projection)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    matrixProjectionCovariance projection w (completeGenerator channel) =
      ∑ v, matrixProjectionCovariance projection w (channel v) := by
  rw [matrixProjectionCovariance_eq_twoPoint projection w _
      hIdempotent hHermitian,
    twoPointCovariance_completeGenerator]
  apply Finset.sum_congr rfl
  intro v _
  rw [matrixProjectionCovariance_eq_twoPoint projection w (channel v)
    hIdempotent hHermitian]

/-- Literal nested outer-minus-Sonin matrix response. -/
noncomputable def signedMatrixProjectionCovariance
    (outerProjection soninProjection : Matrix X X ℂ)
    (w h : X → ℂ) : ℂ :=
  matrixProjectionCovariance outerProjection w h -
    matrixProjectionCovariance soninProjection w h

/-- The complete generator is expanded only inside the signed nested response. -/
theorem signedMatrixProjectionCovariance_completeGenerator
    (outerProjection soninProjection : Matrix X X ℂ)
    (w : X → ℂ) (channel : V → X → ℂ)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y)) :
    signedMatrixProjectionCovariance outerProjection soninProjection w
        (completeGenerator channel) =
      ∑ v, signedMatrixProjectionCovariance outerProjection soninProjection
        w (channel v) := by
  unfold signedMatrixProjectionCovariance
  rw [matrixProjectionCovariance_completeGenerator outerProjection w channel
      hOuterIdempotent hOuterHermitian,
    matrixProjectionCovariance_completeGenerator soninProjection w channel
      hSoninIdempotent hSoninHermitian,
    ← Finset.sum_sub_distrib]

/-- Final finite support-first synchronized owner.  The outer support sum and
inner channel sum stay signed and ordered. -/
theorem signedMatrixProjectionCovariance_support_first_generator
    (outerProjection soninProjection : Matrix X X ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ)
    (channel : V → X → ℂ) (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y)) :
    signedMatrixProjectionCovariance outerProjection soninProjection
        (correlationMultiplier correlation character)
        (completeGenerator channel) =
      ∑ u ∈ support, correlation u *
        ∑ v, signedMatrixProjectionCovariance
          outerProjection soninProjection (character u) (channel v) := by
  unfold signedMatrixProjectionCovariance
  rw [matrixProjectionCovariance_correlation_support outerProjection
      correlation character (completeGenerator channel) support hzero
      hOuterIdempotent hOuterHermitian,
    matrixProjectionCovariance_correlation_support soninProjection
      correlation character (completeGenerator channel) support hzero
      hSoninIdempotent hSoninHermitian,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [matrixProjectionCovariance_completeGenerator outerProjection
      (character u) channel hOuterIdempotent hOuterHermitian,
    matrixProjectionCovariance_completeGenerator soninProjection
      (character u) channel hSoninIdempotent hSoninHermitian]
  calc
    correlation u *
          ∑ v, matrixProjectionCovariance outerProjection
            (character u) (channel v) -
        correlation u *
          ∑ v, matrixProjectionCovariance soninProjection
            (character u) (channel v) =
        correlation u *
          ((∑ v, matrixProjectionCovariance outerProjection
              (character u) (channel v)) -
            ∑ v, matrixProjectionCovariance soninProjection
              (character u) (channel v)) := by ring
    _ = correlation u *
        ∑ v, (matrixProjectionCovariance outerProjection
            (character u) (channel v) -
          matrixProjectionCovariance soninProjection
            (character u) (channel v)) := by
      rw [Finset.sum_sub_distrib]

end CCM24FiniteSSynchronizedCovariance
end CCM25Concrete
end Source
end ConnesWeilRH
