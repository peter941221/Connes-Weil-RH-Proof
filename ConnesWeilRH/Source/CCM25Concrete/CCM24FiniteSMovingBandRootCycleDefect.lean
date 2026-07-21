/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandMatrixCancellation

/-!
# Root-cycle defects for the complete moving crossing

Finite-prefix cyclicity moves the right convolution root to the left of the
complete crossing.  The result is the genuine positive detector acting on
the still-recombined five-branch crossing, plus one explicit antisymmetric
prefix-product defect.  The two terms remain inside one signed integrand.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandRootCycleDefect

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCompletedMovingCrossing
open CCM24FiniteSMovingBandEndpointIntegral
open CCM24FiniteSMovingBandMatrixCancellation
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSPrefixBoundaryDefect

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- Antisymmetric defect left by one finite-prefix cyclic permutation. -/
noncomputable def basisPrefixCycleDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) : Matrix (Fin N) (Fin N) ℂ :=
  basisPrefixProductDefect basis N left right -
    basisPrefixProductDefect basis N right left

/-- A finite-prefix product trace cycles with exactly one boundary defect. -/
theorem trace_basisPrefixMatrix_product_eq_cycled_add_boundaryDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) :
    Matrix.trace (basisPrefixMatrix basis N (left * right)) =
      Matrix.trace (basisPrefixMatrix basis N (right * left)) +
        Matrix.trace (basisPrefixCycleDefect basis N left right) := by
  unfold basisPrefixCycleDefect basisPrefixProductDefect
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm]
  ring

/-- Cyclic rotation of a triple product keeps the entire first two factors
together and records only the outer cycle boundary. -/
theorem trace_basisPrefixMatrix_tripleProduct_eq_cycled_add_boundaryDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left middle right : H →L[ℂ] H) :
    Matrix.trace (basisPrefixMatrix basis N (left * middle * right)) =
      Matrix.trace (basisPrefixMatrix basis N (right * (left * middle))) +
        Matrix.trace
          (basisPrefixCycleDefect basis N (left * middle) right) := by
  exact trace_basisPrefixMatrix_product_eq_cycled_add_boundaryDefect
    basis N (left * middle) right

/-- The unsandwiched actual complete five-branch crossing. -/
noncomputable def actualCompletedMovingCrossingCore
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) : Op :=
  completedMovingCrossing
    (radialSupportProjection lambda)
    (CCM24FiniteSParameterizedSoninProjection.parameterizedFourierSupportProjection
      lambda alpha S halpha)
    (CCM24FiniteSParameterizedSoninProjection.parameterizedProlateRemainder
      lambda alpha S halpha)
    (CCM24FiniteSParameterizedEulerGenerator.parameterizedFiniteEulerGenerator
      alpha S)

theorem actualCompletedRootCrossing_eq_root_mul_core_mul_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    actualCompletedRootCrossing owner lambda alpha S halpha =
      rootConvolution owner *
        actualCompletedMovingCrossingCore lambda alpha S halpha *
          (rootConvolution owner).adjoint := by
  rfl

/-- Boundary term left by cycling the right convolution root around the
finite prefix. -/
noncomputable def actualCompletedRootCycleDefect
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    Matrix (Fin N) (Fin N) ℂ :=
  basisPrefixCycleDefect basis N
    (rootConvolution owner *
      actualCompletedMovingCrossingCore lambda alpha S halpha)
    (rootConvolution owner).adjoint

/-- The root-sandwiched complete trace is the detector-weighted complete
crossing plus its explicit finite-prefix cycle defect. -/
theorem trace_actualCompletedRootCrossing_eq_detectorCore_add_cycleDefect
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    Matrix.trace (basisPrefixMatrix basis N
        (actualCompletedRootCrossing owner lambda alpha S halpha)) =
      Matrix.trace (basisPrefixMatrix basis N
        (detectorOperator owner *
          actualCompletedMovingCrossingCore lambda alpha S halpha)) +
        Matrix.trace
          (actualCompletedRootCycleDefect basis N owner lambda alpha S halpha) := by
  rw [actualCompletedRootCrossing_eq_root_mul_core_mul_adjoint]
  have hcycle :=
    trace_basisPrefixMatrix_tripleProduct_eq_cycled_add_boundaryDefect
      basis N (rootConvolution owner)
        (actualCompletedMovingCrossingCore lambda alpha S halpha)
        (rootConvolution owner).adjoint
  have hdetector :
      (rootConvolution owner).adjoint *
          (rootConvolution owner *
            actualCompletedMovingCrossingCore lambda alpha S halpha) =
        detectorOperator owner *
          actualCompletedMovingCrossingCore lambda alpha S halpha := by
    calc
      (rootConvolution owner).adjoint *
          (rootConvolution owner *
            actualCompletedMovingCrossingCore lambda alpha S halpha) =
          ((rootConvolution owner).adjoint * rootConvolution owner) *
            actualCompletedMovingCrossingCore lambda alpha S halpha := by
        rw [mul_assoc]
      _ = detectorOperator owner *
            actualCompletedMovingCrossingCore lambda alpha S halpha := by
        rfl
  rw [hdetector] at hcycle
  simpa only [actualCompletedRootCycleDefect] using hcycle

theorem trace_actualCompletedRootCrossing_re_eq_detectorCore_add_cycleDefect_re
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (Matrix.trace (basisPrefixMatrix basis N
      (actualCompletedRootCrossing owner lambda alpha S halpha))).re =
      (Matrix.trace (basisPrefixMatrix basis N
        (detectorOperator owner *
          actualCompletedMovingCrossingCore lambda alpha S halpha))).re +
        (Matrix.trace
          (actualCompletedRootCycleDefect basis N owner lambda alpha S halpha)).re := by
  simpa only [Complex.add_re] using congrArg Complex.re
    (trace_actualCompletedRootCrossing_eq_detectorCore_add_cycleDefect
      basis N owner lambda alpha S halpha)

/-- Total core representative matching the legal crossing on `[-1,1]`. -/
noncomputable def actualCompletedMovingCrossingCoreOnUnit
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  if halpha : |alpha| ≤ 1 then
    actualCompletedMovingCrossingCore lambda alpha S halpha
  else 0

theorem actualCompletedMovingCrossingCoreOnUnit_eq
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    actualCompletedMovingCrossingCoreOnUnit lambda alpha S =
      actualCompletedMovingCrossingCore lambda alpha S halpha := by
  simp only [actualCompletedMovingCrossingCoreOnUnit, dif_pos halpha]

/-- The complete signed scalar after cycling the right root.  The physical
detector term and prefix-cycle defect remain recombined. -/
noncomputable def actualCompletedWeightedBoundaryTrace
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : ℝ :=
  let core := actualCompletedMovingCrossingCoreOnUnit lambda alpha S
  (Matrix.trace (basisPrefixMatrix basis N
    (detectorOperator owner * core))).re +
    (Matrix.trace (basisPrefixCycleDefect basis N
      (rootConvolution owner * core) (rootConvolution owner).adjoint)).re

theorem trace_actualCompletedRootCrossingOnUnit_re_eq_weightedBoundaryTrace
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (Matrix.trace (basisPrefixMatrix basis N
      (actualCompletedRootCrossingOnUnit owner lambda alpha S))).re =
      actualCompletedWeightedBoundaryTrace basis N owner lambda alpha S := by
  rw [actualCompletedRootCrossingOnUnit_eq owner lambda alpha S halpha]
  unfold actualCompletedWeightedBoundaryTrace
  dsimp only
  rw [actualCompletedMovingCrossingCoreOnUnit_eq lambda alpha S halpha]
  exact
    trace_actualCompletedRootCrossing_re_eq_detectorCore_add_cycleDefect_re
      basis N owner lambda alpha S halpha

/-- The complete-crossing integral is exactly the integral of the recombined
detector core and root-cycle defect. -/
theorem integral_trace_actualCompletedRootCrossingOnUnit_re_eq_weightedBoundaryTrace
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (∫ alpha : ℝ in 0..1,
      (Matrix.trace (basisPrefixMatrix basis N
        (actualCompletedRootCrossingOnUnit owner lambda alpha S))).re) =
      ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace basis N owner lambda alpha S := by
  apply intervalIntegral.integral_congr
  intro alpha halpha
  have hzero_one : (0 : ℝ) ≤ 1 := by norm_num
  rw [Set.uIcc_of_le hzero_one] at halpha
  have habs : |alpha| ≤ 1 := abs_le.mpr ⟨by linarith [halpha.1], halpha.2⟩
  exact trace_actualCompletedRootCrossingOnUnit_re_eq_weightedBoundaryTrace
    basis N owner lambda alpha S habs

/-- The active canonical Gate 3U consumer may use one bound on the recombined
detector core plus prefix-cycle defect. -/
theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_weightedBoundaryBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda
        (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner)))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace basis N owner lambda alpha
          (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner).visiblePrimes| ≤
        (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda
        (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  apply
    canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_completeBound
      basis owner lambda htrace
  intro N
  rw [integral_trace_actualCompletedRootCrossingOnUnit_re_eq_weightedBoundaryTrace]
  exact hbound N

end CCM24FiniteSMovingBandRootCycleDefect
end CCM25Concrete
end Source
end ConnesWeilRH
