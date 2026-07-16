/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingSupportFirst

/-!
# Completed finite-S Sonin kernel

The identity `R = E Q E - K_prol` is inserted into the support-first moving
kernel without dropping `K_prol`.  Its square produces both prolate cross
terms and the prolate square; all five terms remain in one signed kernel.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedSoninKernel

open scoped BigOperators ComplexConjugate Matrix
open CCM24FiniteSSupportFirstCovariance
open CCM24FiniteSSynchronizedCovariance
open CCM24FiniteSMovingProjectionCovariance
open CCM24FiniteSMovingSupportFirst

variable {X U V : Type*} [Fintype X] [DecidableEq X]
  [Fintype U] [Fintype V]

/-- The compressed second-support kernel `E Q E`. -/
noncomputable def compressedSecondSupportKernel
    (outerProjection secondSupport : Matrix X X ℂ) : Matrix X X ℂ :=
  outerProjection * secondSupport * outerProjection

/-- The complete `E-(E Q E-K_prol)` projection-kernel mass.  The middle two
terms are the prolate interference terms and cannot be omitted. -/
noncomputable def completedSoninKernelMass
    (outerProjection secondSupport prolateRemainder : Matrix X X ℂ)
    (x y : X) : ℂ :=
  let compressed := compressedSecondSupportKernel
    outerProjection secondSupport
  projectionKernelMass outerProjection x y -
      projectionKernelMass compressed x y +
    conj (compressed x y) * prolateRemainder x y +
    conj (prolateRemainder x y) * compressed x y -
    projectionKernelMass prolateRemainder x y

omit [DecidableEq X] in
/-- Pointwise readback of the completed Sonin kernel. -/
theorem completedSoninKernelMass_eq_signed_projectionKernelMass
    (outerProjection secondSupport soninProjection prolateRemainder :
      Matrix X X ℂ)
    (hSonin : soninProjection =
      compressedSecondSupportKernel outerProjection secondSupport -
        prolateRemainder) (x y : X) :
    completedSoninKernelMass outerProjection secondSupport prolateRemainder
        x y =
      projectionKernelMass outerProjection x y -
        projectionKernelMass soninProjection x y := by
  rw [hSonin]
  simp only [completedSoninKernelMass, projectionKernelMass, map_sub,
    Matrix.sub_apply]
  ring

omit [DecidableEq X] in
/-- The signed outer-minus-Sonin covariance is exactly the covariance of the
five-term completed kernel. -/
theorem signedTwoPointCovariance_eq_completedSoninKernel
    (outerProjection secondSupport soninProjection prolateRemainder :
      Matrix X X ℂ)
    (w h : X → ℂ)
    (hSonin : soninProjection =
      compressedSecondSupportKernel outerProjection secondSupport -
        prolateRemainder) :
    signedTwoPointCovariance
        (projectionKernelMass outerProjection)
        (projectionKernelMass soninProjection) w h =
      twoPointCovariance
        (completedSoninKernelMass outerProjection secondSupport
          prolateRemainder) w h := by
  classical
  unfold signedTwoPointCovariance twoPointCovariance
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [completedSoninKernelMass_eq_signed_projectionKernelMass
    outerProjection secondSupport soninProjection prolateRemainder
    hSonin x y]
  ring

/-- Literal finite projection traces read back to the completed CC20 kernel. -/
theorem signedMatrixProjectionCovariance_eq_completedSoninKernel
    (outerProjection secondSupport soninProjection prolateRemainder :
      Matrix X X ℂ)
    (w h : X → ℂ)
    (hSonin : soninProjection =
      compressedSecondSupportKernel outerProjection secondSupport -
        prolateRemainder)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y)) :
    signedMatrixProjectionCovariance outerProjection soninProjection w h =
      twoPointCovariance
        (completedSoninKernelMass outerProjection secondSupport
          prolateRemainder) w h := by
  unfold signedMatrixProjectionCovariance
  rw [matrixProjectionCovariance_eq_twoPoint outerProjection w h
      hOuterIdempotent hOuterHermitian,
    matrixProjectionCovariance_eq_twoPoint soninProjection w h
      hSoninIdempotent hSoninHermitian]
  exact signedTwoPointCovariance_eq_completedSoninKernel outerProjection
    secondSupport soninProjection prolateRemainder w h hSonin

/-- Final finite support-first moving owner after inserting
`R = E Q E-K_prol`.  The five completed kernel branches remain inside both
finite sums and under one real part. -/
theorem signedMovingProjectionTraceResponse_support_first_completedSonin
    (outerProjection secondSupport soninProjection prolateRemainder :
      Matrix X X ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ)
    (channel : V → X → ℂ) (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0)
    (hSonin : soninProjection =
      compressedSecondSupportKernel outerProjection secondSupport -
        prolateRemainder)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y))
    (hDetectorReal : ∀ x,
      conj (correlationMultiplier correlation character x) =
        correlationMultiplier correlation character x) :
    signedMovingProjectionTraceResponse outerProjection soninProjection
        (correlationMultiplier correlation character)
        (completeGenerator channel) =
      (2 * Complex.re
        (∑ u ∈ support, correlation u *
          ∑ v, twoPointCovariance
            (completedSoninKernelMass outerProjection secondSupport
              prolateRemainder) (character u) (channel v)) : ℝ) := by
  rw [signedMovingProjectionTraceResponse_support_first_generator
      outerProjection soninProjection correlation character channel support
      hzero hOuterIdempotent hSoninIdempotent hOuterHermitian
      hSoninHermitian hDetectorReal]
  congr 3
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact signedMatrixProjectionCovariance_eq_completedSoninKernel
    outerProjection secondSupport soninProjection prolateRemainder
    (character u) (channel v) hSonin hOuterIdempotent hSoninIdempotent
    hOuterHermitian hSoninHermitian

end CCM24FiniteSCompletedSoninKernel
end CCM25Concrete
end Source
end ConnesWeilRH
