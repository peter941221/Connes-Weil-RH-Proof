/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalRenewalExpansion

/-!
# Support-first two-point covariance algebra

This module formalizes the finite algebra behind the correct Gate 3U support
order.  A compact root is first reconstructed from its finitely supported
cross-correlation, and only then paired with the complete signed two-point
kernel.  No translated projection trace and no branchwise absolute value is
introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSupportFirstCovariance

open scoped BigOperators ComplexConjugate

variable {X U : Type*} [Fintype X] [Fintype U]

/-- The oriented two-point covariance attached to a kernel mass. -/
noncomputable def twoPointCovariance
    (mass : X → X → ℂ) (w h : X → ℂ) : ℂ :=
  ∑ x, ∑ y, w x * (h x - h y) * mass x y

/-- The symmetric finite-difference form of the same covariance. -/
noncomputable def symmetricTwoPointCovariance
    (mass : X → X → ℂ) (w h : X → ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ∑ x, ∑ y, (w x - w y) * (h x - h y) * mass x y

/-- Symmetric kernel mass turns the oriented covariance into two finite
differences.  This is the algebraic form in which coherent scalar components
cancel before any estimate. -/
theorem twoPointCovariance_eq_symmetric
    (mass : X → X → ℂ) (w h : X → ℂ)
    (hmass : ∀ x y, mass y x = mass x y) :
    twoPointCovariance mass w h =
      symmetricTwoPointCovariance mass w h := by
  classical
  let oriented : ℂ := ∑ x, ∑ y,
    w x * (h x - h y) * mass x y
  let reflected : ℂ := ∑ x, ∑ y,
    w y * (h y - h x) * mass x y
  have hreflect : oriented = reflected := by
    dsimp [oriented, reflected]
    calc
      (∑ x, ∑ y, w x * (h x - h y) * mass x y) =
          ∑ y, ∑ x, w x * (h x - h y) * mass x y :=
        Finset.sum_comm
      _ = ∑ x, ∑ y, w y * (h y - h x) * mass x y := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [hmass x y]
  have hdouble :
      (2 : ℂ) * oriented =
        ∑ x, ∑ y, (w x - w y) * (h x - h y) * mass x y := by
    calc
      (2 : ℂ) * oriented = oriented + oriented := by ring
      _ = oriented + reflected := by rw [hreflect]
      _ = (∑ x, ∑ y,
            w x * (h x - h y) * mass x y) +
          ∑ x, ∑ y,
            w y * (h y - h x) * mass x y := by
        rfl
      _ = ∑ x, ∑ y,
          (w x * (h x - h y) * mass x y +
            w y * (h y - h x) * mass x y) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib]
      _ = ∑ x, ∑ y,
          (w x - w y) * (h x - h y) * mass x y := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
  change oriented = (1 / 2 : ℂ) * _
  rw [← hdouble]
  ring

theorem twoPointCovariance_const_left
    (mass : X → X → ℂ) (c : ℂ) (h : X → ℂ) :
    symmetricTwoPointCovariance mass (fun _ => c) h = 0 := by
  classical
  simp [symmetricTwoPointCovariance]

theorem twoPointCovariance_const_right
    (mass : X → X → ℂ) (w : X → ℂ) (c : ℂ) :
    symmetricTwoPointCovariance mass w (fun _ => c) = 0 := by
  classical
  simp [symmetricTwoPointCovariance]

/-- Fourier reconstruction of a detector multiplier from displacement
coefficients. -/
noncomputable def correlationMultiplier
    (correlation : U → ℂ) (character : U → X → ℂ) (x : X) : ℂ :=
  ∑ u, correlation u * character u x

/-- Support enters before the displacement modes are separated: the complete
covariance against a reconstructed multiplier is the signed sum of the mode
covariances. -/
theorem twoPointCovariance_correlationMultiplier
    (mass : X → X → ℂ) (correlation : U → ℂ)
    (character : U → X → ℂ) (h : X → ℂ) :
    twoPointCovariance mass
        (correlationMultiplier correlation character) h =
      ∑ u, correlation u *
        twoPointCovariance mass (character u) h := by
  classical
  unfold twoPointCovariance correlationMultiplier
  simp_rw [Finset.sum_mul]
  calc
    (∑ x, ∑ y, ∑ u,
        correlation u * character u x * (h x - h y) * mass x y) =
        ∑ x, ∑ u, ∑ y,
          correlation u * character u x * (h x - h y) * mass x y := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ u, ∑ x, ∑ y,
          correlation u * character u x * (h x - h y) * mass x y :=
      Finset.sum_comm
    _ = ∑ u, correlation u *
          ∑ x, ∑ y, character u x * (h x - h y) * mass x y := by
      apply Finset.sum_congr rfl
      intro u _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- If the correlation vanishes outside a finite displacement window, the
complete covariance is indexed only by that window.  The restriction is made
before an absolute value and before a prime or branch split. -/
theorem twoPointCovariance_correlation_support
    (mass : X → X → ℂ) (correlation : U → ℂ)
    (character : U → X → ℂ) (h : X → ℂ)
    (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0) :
    twoPointCovariance mass
        (correlationMultiplier correlation character) h =
      ∑ u ∈ support, correlation u *
        twoPointCovariance mass (character u) h := by
  rw [twoPointCovariance_correlationMultiplier]
  symm
  apply Finset.sum_subset (Finset.subset_univ support)
  intro u _ husupport
  simp [hzero u husupport]

/-- Signed outer-minus-Sonin covariance. -/
noncomputable def signedTwoPointCovariance
    (outerMass soninMass : X → X → ℂ) (w h : X → ℂ) : ℂ :=
  twoPointCovariance outerMass w h -
    twoPointCovariance soninMass w h

/-- Compact correlation support is applied to the whole signed nested kernel,
not separately to its outer and Sonin terms. -/
theorem signedTwoPointCovariance_correlation_support
    (outerMass soninMass : X → X → ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ) (h : X → ℂ)
    (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0) :
    signedTwoPointCovariance outerMass soninMass
        (correlationMultiplier correlation character) h =
      ∑ u ∈ support, correlation u *
        signedTwoPointCovariance outerMass soninMass (character u) h := by
  unfold signedTwoPointCovariance
  rw [twoPointCovariance_correlation_support outerMass correlation character h
      support hzero,
    twoPointCovariance_correlation_support soninMass correlation character h
      support hzero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Kernel mass of a complex projection matrix. -/
noncomputable def projectionKernelMass
    (projection : X → X → ℂ) (x y : X) : ℂ :=
  conj (projection x y) * projection x y

omit [Fintype X] in
/-- Hermitian projection kernels have symmetric two-point mass. -/
theorem projectionKernelMass_symmetric
    (projection : X → X → ℂ)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    ∀ x y, projectionKernelMass projection y x =
      projectionKernelMass projection x y := by
  intro x y
  unfold projectionKernelMass
  calc
    conj (projection y x) * projection y x =
        (Complex.normSq (projection y x) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    _ = (Complex.normSq (conj (projection x y)) : ℂ) := by
      rw [hHermitian]
    _ = (Complex.normSq (projection x y) : ℂ) := by
      rw [Complex.normSq_conj]
    _ = conj (projection x y) * projection x y :=
      Complex.normSq_eq_conj_mul_self

/-- The projection-kernel covariance therefore has the exact symmetric
finite-difference readback. -/
theorem projectionKernelCovariance_eq_symmetric
    (projection : X → X → ℂ) (w h : X → ℂ)
    (hHermitian : ∀ x y, projection y x = conj (projection x y)) :
    twoPointCovariance (projectionKernelMass projection) w h =
      symmetricTwoPointCovariance (projectionKernelMass projection) w h :=
  twoPointCovariance_eq_symmetric _ _ _
    (projectionKernelMass_symmetric projection hHermitian)

end CCM24FiniteSSupportFirstCovariance
end CCM25Concrete
end Source
end ConnesWeilRH
