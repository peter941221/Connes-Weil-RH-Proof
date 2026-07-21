/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPrefixBoundaryDefect
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandEndpointIntegral

/-!
# Finite-matrix cancellation for the complete moving band

The Hermitian moving flow is compressed as one finite matrix.  Its adjoint
branch becomes the conjugate transpose of the same complete five-branch
crossing matrix, so its signed trace is exactly twice one real trace.  No
branchwise absolute value or infinite-dimensional trace cycle is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandMatrixCancellation

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSMovingBandDiagonalIntegral
open CCM24FiniteSMovingBandEndpointIntegral
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSRootSandwichedMovingFlow

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- Compression intertwines the Hilbert adjoint with matrix conjugate
transpose. -/
theorem basisPrefixMatrix_adjoint_eq_conjTranspose
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (operator : H →L[ℂ] H) :
    basisPrefixMatrix basis N operator.adjoint =
      (basisPrefixMatrix basis N operator)ᴴ := by
  ext i j
  simp only [basisPrefixMatrix, Matrix.conjTranspose_apply, Complex.star_def]
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (operator (basis i)) (basis j)).symm

/-- The entire moving flow matrix is the negative complete crossing matrix
minus its conjugate transpose. -/
theorem basisPrefixMatrix_actualMovingSoninRootFlow_eq_neg_complete_sub_conjTranspose
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) (N : ℕ) :
    basisPrefixMatrix basis N
        (actualMovingSoninRootFlow owner lambda alpha S) =
      -basisPrefixMatrix basis N
          (actualCompletedRootCrossing owner lambda alpha S halpha) -
        (basisPrefixMatrix basis N
          (actualCompletedRootCrossing owner lambda alpha S halpha))ᴴ := by
  rw [actualMovingSoninRootFlow_eq_neg_completedRootCrossing_add_adjoint
    owner lambda alpha S halpha]
  ext i j
  simp only [basisPrefixMatrix, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, inner_sub_right, inner_neg_right,
    Matrix.sub_apply, Matrix.neg_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hinner := (inner_conj_symm (𝕜 := ℂ)
    (actualCompletedRootCrossing owner lambda alpha S halpha (basis i))
    (basis j)).symm
  rw [hinner]

/-- The signed finite trace keeps the complete five-branch crossing whole. -/
theorem trace_basisPrefixMatrix_actualMovingSoninRootFlow_re_eq_neg_two_complete_re
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) (N : ℕ) :
    (Matrix.trace (basisPrefixMatrix basis N
      (actualMovingSoninRootFlow owner lambda alpha S))).re =
      -2 * (Matrix.trace (basisPrefixMatrix basis N
        (actualCompletedRootCrossing owner lambda alpha S halpha))).re := by
  rw [basisPrefixMatrix_actualMovingSoninRootFlow_eq_neg_complete_sub_conjTranspose
    basis owner lambda alpha S halpha N]
  rw [Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_conjTranspose]
  simp only [Complex.star_def, Complex.sub_re, Complex.neg_re, Complex.conj_re]
  ring

/-- A total representative of the complete crossing.  Outside the legal
parameter interval it is zero; interval integrals below only use `[0,1]`. -/
noncomputable def actualCompletedRootCrossingOnUnit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  if halpha : |alpha| ≤ 1 then
    actualCompletedRootCrossing owner lambda alpha S halpha
  else 0

theorem actualCompletedRootCrossingOnUnit_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    actualCompletedRootCrossingOnUnit owner lambda alpha S =
      actualCompletedRootCrossing owner lambda alpha S halpha := by
  simp only [actualCompletedRootCrossingOnUnit, dif_pos halpha]

/-- On `[0,1]`, the finite moving-flow trace is exactly negative twice the
real trace of the completed crossing matrix. -/
theorem integral_trace_basisPrefixMatrix_actualMovingSoninRootFlow_re_eq_neg_two_complete
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (N : ℕ) :
    (∫ alpha : ℝ in 0..1,
      (Matrix.trace (basisPrefixMatrix basis N
        (actualMovingSoninRootFlow owner lambda alpha S))).re) =
      -2 * ∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualCompletedRootCrossingOnUnit owner lambda alpha S))).re := by
  calc
    (∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualMovingSoninRootFlow owner lambda alpha S))).re) =
        ∫ alpha : ℝ in 0..1,
          -2 * (Matrix.trace (basisPrefixMatrix basis N
            (actualCompletedRootCrossingOnUnit owner lambda alpha S))).re := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      have hzero_one : (0 : ℝ) ≤ 1 := by norm_num
      rw [Set.uIcc_of_le hzero_one] at halpha
      have habs : |alpha| ≤ 1 := abs_le.mpr ⟨by linarith [halpha.1], halpha.2⟩
      change
        (Matrix.trace (basisPrefixMatrix basis N
          (actualMovingSoninRootFlow owner lambda alpha S))).re =
          -2 * (Matrix.trace (basisPrefixMatrix basis N
            (actualCompletedRootCrossingOnUnit owner lambda alpha S))).re
      rw [actualCompletedRootCrossingOnUnit_eq owner lambda alpha S habs]
      exact
        trace_basisPrefixMatrix_actualMovingSoninRootFlow_re_eq_neg_two_complete_re
          basis owner lambda alpha S habs N
    _ = -2 * ∫ alpha : ℝ in 0..1,
          (Matrix.trace (basisPrefixMatrix basis N
            (actualCompletedRootCrossingOnUnit owner lambda alpha S))).re := by
      rw [intervalIntegral.integral_const_mul]

/-- The finite endpoint response is twice the integrated complete crossing
trace.  This is an exact signed identity, not a norm estimate. -/
theorem trace_basisPrefixMatrix_bandResponse_re_eq_two_integral_complete
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (N : ℕ) :
    (Matrix.trace (basisPrefixMatrix basis N
      (rootSandwichedBandResponse owner lambda family))).re =
      2 * ∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualCompletedRootCrossingOnUnit owner lambda alpha
            family.visiblePrimes))).re := by
  have hendpoint :=
    finiteDiagonalResponse_re_eq_neg_integral_finiteDiagonalFlow_re
      basis (Finset.range N) owner lambda family
  have hflow :
      (∫ alpha : ℝ in 0..1,
        ∑ i ∈ Finset.range N,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re) =
        ∫ alpha : ℝ in 0..1,
          (Matrix.trace (basisPrefixMatrix basis N
            (actualMovingSoninRootFlow owner lambda alpha
              family.visiblePrimes))).re := by
    apply intervalIntegral.integral_congr
    intro alpha _halpha
    exact (trace_basisPrefixMatrix_re_eq_rangeDiagonal_re basis N
      (actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)).symm
  rw [← trace_basisPrefixMatrix_re_eq_rangeDiagonal_re] at hendpoint
  rw [hflow] at hendpoint
  rw [integral_trace_basisPrefixMatrix_actualMovingSoninRootFlow_re_eq_neg_two_complete
    basis owner lambda family.visiblePrimes N] at hendpoint
  linarith

/-- It suffices to bound the integrated complete five-branch finite trace by
the undoubled support-radius polynomial. -/
theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_completeBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualCompletedRootCrossingOnUnit owner lambda alpha
            (canonicalFamily owner).visiblePrimes))).re| ≤
        (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  apply
    canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_prefixCompressionBound
      basis owner lambda htrace
  intro N
  rw [integral_trace_basisPrefixMatrix_actualMovingSoninRootFlow_re_eq_neg_two_complete
    basis owner lambda (canonicalFamily owner).visiblePrimes N]
  calc
    |-2 * ∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualCompletedRootCrossingOnUnit owner lambda alpha
            (canonicalFamily owner).visiblePrimes))).re| =
        2 * |∫ alpha : ℝ in 0..1,
          (Matrix.trace (basisPrefixMatrix basis N
            (actualCompletedRootCrossingOnUnit owner lambda alpha
              (canonicalFamily owner).visiblePrimes))).re| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ((owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) := by
      exact mul_le_mul_of_nonneg_left (hbound N) (by norm_num)
    _ = 2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3) := by ring

end CCM24FiniteSMovingBandMatrixCancellation
end CCM25Concrete
end Source
end ConnesWeilRH
