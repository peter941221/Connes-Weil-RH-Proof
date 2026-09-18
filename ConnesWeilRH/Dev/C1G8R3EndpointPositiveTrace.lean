/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge

/-!
# Positive trace of the endpoint limit

The endpoint operator is not merely known to be positive as an abstract
operator.  After the survivor-core square-sum is supplied, it is the positive
composition of one explicit source-side Hilbert--Schmidt factor.  This leaf
therefore closes the sign half of the endpoint readback and leaves only the
survivor-core energy estimate.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.C1PositiveTraceLimitBridge
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance endpointPositiveTraceSourceCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The endpoint limit is the positive composition of the explicit source
factor obtained by inserting the oblique shear between two root convolutions. -/
theorem g8EndpointSourceCutoffLimitOperator_eq_sourcePositiveComposition
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8EndpointSourceCutoffLimitOperator owner lambda family =
      let factor :=
        rootConvolution owner ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier +
            (finiteEulerPulledObliqueShear lambda family)†) ∘L
          rootConvolution owner ∘L sourceInclusion lambda
      factor† ∘L factor := by
  let C := rootConvolution owner
  let A := ContinuousLinearMap.id ℂ finiteSCarrier +
    (finiteEulerPulledObliqueShear lambda family)†
  let J := sourceInclusion lambda
  change J† ∘L C† ∘L (A† ∘L
      detectorOperator owner ∘L A) ∘L C ∘L J = _
  rw [detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    C, A, J]

/-- The endpoint trace is nonnegative once the survivor-core energy gate is
available.  No positivity or summability premise is hidden: the former is a
square, and the latter is obtained from the exact gate equivalence. -/
theorem g8EndpointSourceCutoffLimitOperator_trace_re_nonnegative_of_survivorCore
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (g8EndpointSourceCutoffLimitOperator owner lambda family)).re := by
  let C := rootConvolution owner
  let A := ContinuousLinearMap.id ℂ finiteSCarrier +
    (finiteEulerPulledObliqueShear lambda family)†
  let J := sourceInclusion lambda
  let factor := C ∘L A ∘L C ∘L J
  have hgate : Summable fun i : ρ =>
      ‖C (J (sourceBasis i))‖ ^ 2 := by
    simpa only [C, J, ContinuousLinearMap.comp_apply] using
      ((g8EndpointGate_iff_survivorCore owner lambda sourceBasis).mpr hcore)
  have hfactor : Summable fun i : ρ =>
      ‖factor (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis
      (C ∘L J) (C ∘L A) hgate
  let data : BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
    { left := factor
      right := factor
      left_summable_normSq := hfactor
      right_summable_normSq := hfactor }
  have heq : data.traceProduct =
      g8EndpointSourceCutoffLimitOperator owner lambda family := by
    rw [g8EndpointSourceCutoffLimitOperator_eq_sourcePositiveComposition]
    rfl
  rw [← heq]
  exact positiveTracePair_re_nonnegative_of_self data rfl

end Dev
end ConnesWeilRH
