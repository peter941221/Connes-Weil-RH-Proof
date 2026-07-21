/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointBalancedCycle

/-!
# Endpoint arithmetic ledger on a finite target prefix

The target-prefix response from Proof 461 cycles the right convolution root
only inside the finite compression.  The resulting detector response is the
existing same-object arithmetic operator plus its canonical residual.  The
finite root-cycle defect is retained with that residual as one completed
remainder.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointArithmeticLedger

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSMovingBandRootCycleDefect
open CCM24FiniteSRectangularPrefixCycle
open CCM24FiniteSEndpointBalancedCycle

/-- The exact finite-prefix defect left by cycling the right root around the
endpoint Sonin-band difference. -/
noncomputable def actualBandEndpointRootCycleDefect
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    Matrix (Fin N) (Fin N) ℂ :=
  basisPrefixCycleDefect basis N
    (rootConvolution owner * soninBandDifference lambda family)
    (rootConvolution owner).adjoint

/-- The finite target-prefix root sandwich cycles to the detector response
with one explicit endpoint defect. -/
theorem trace_targetPrefixRootResponse_eq_projectionResponse_add_cycleDefect
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix basis N
        (rootSandwichedBandResponse owner lambda family)) =
      Matrix.trace (basisPrefixMatrix basis N
        (projectionResponse owner lambda family)) +
        Matrix.trace
          (actualBandEndpointRootCycleDefect basis N owner lambda family) := by
  have hcycle := trace_basisPrefixMatrix_tripleProduct_eq_cycled_add_boundaryDefect
    basis N (rootConvolution owner) (soninBandDifference lambda family)
      (rootConvolution owner).adjoint
  have hdetector :
      (rootConvolution owner).adjoint *
          (rootConvolution owner * soninBandDifference lambda family) =
        detectorOperator owner * soninBandDifference lambda family := by
    calc
      (rootConvolution owner).adjoint *
          (rootConvolution owner * soninBandDifference lambda family) =
        ((rootConvolution owner).adjoint * rootConvolution owner) *
          soninBandDifference lambda family := by
        rw [mul_assoc]
      _ = detectorOperator owner * soninBandDifference lambda family := by
        rfl
  rw [hdetector] at hcycle
  simpa only [rootSandwichedBandResponse, projectionResponse,
    actualBandEndpointRootCycleDefect, ContinuousLinearMap.mul_def] using hcycle

/-- The canonical endpoint remainder keeps the same-object residual and the
finite root-cycle defect together. -/
noncomputable def actualBandEndpointCompletedResidualTrace
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : ℂ :=
  Matrix.trace (basisPrefixMatrix basis N
      (sameObjectResidual owner lambda family)) +
    Matrix.trace
      (actualBandEndpointRootCycleDefect basis N owner lambda family)

/-- The target-prefix endpoint response is the arithmetic prefix plus one
completed residual. -/
theorem trace_targetPrefixRootResponse_eq_arithmetic_add_completedResidual
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix basis N
        (rootSandwichedBandResponse owner lambda family)) =
      Matrix.trace (basisPrefixMatrix basis N
        (arithmeticOperator owner family)) +
        actualBandEndpointCompletedResidualTrace basis N owner lambda family := by
  have hcycle :=
    trace_targetPrefixRootResponse_eq_projectionResponse_add_cycleDefect
      basis N owner lambda family
  rw [projectionResponse_eq_arithmetic_add_residual] at hcycle
  simp only [basisPrefixMatrix_add, Matrix.trace_add] at hcycle
  unfold actualBandEndpointCompletedResidualTrace
  simpa only [add_assoc] using hcycle

/-- Proof 461's complete weighted endpoint integral has the same finite
arithmetic-plus-completed-residual ledger. -/
theorem two_integral_weightedBoundary_eq_arithmetic_add_completedResidual_re
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace basis N owner lambda
          alpha family.visiblePrimes =
      (Matrix.trace (basisPrefixMatrix basis N
        (arithmeticOperator owner family))).re +
        (actualBandEndpointCompletedResidualTrace basis N owner lambda family).re := by
  rw [← targetPrefixRootResponse_eq_two_integral_weightedBoundary
    basis lambda sourceBasis N sourceN owner family]
  simpa only [Complex.add_re] using congrArg Complex.re
    (trace_targetPrefixRootResponse_eq_arithmetic_add_completedResidual
      basis N owner lambda family)

end CCM24FiniteSEndpointArithmeticLedger
end CCM25Concrete
end Source
end ConnesWeilRH
