/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# Exact radial-boundary and internal-gap split for a Sonin leakage

The complementary output of an ambient operator on a Sonin input splits into
the part outside radial support and the remaining part inside radial support
but outside the Sonin projection. The first is the finite-width radial
boundary candidate; the second is the internal support gap. This is an exact
operator identity only, with no trace-ideal estimate asserted.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open scoped InnerProduct InnerProductSpace

noncomputable local instance radialGapSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Generic two-channel decomposition relative to the nested Sonin and radial
projections. -/
theorem radialSoninComplement_comp_operator_comp_input_eq_boundary_add_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (lambda : CCM24SoninScale) (input : H →L[ℂ] finiteSCarrier)
    (operator : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        operator ∘L input =
      ((ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
          operator ∘L input) +
        ((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L operator ∘L input) := by
  have hradial : radialSupportProjection lambda ∘L
      radialSupportProjection lambda = radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hsourceRadial :=
    sourceSoninProjection_comp_radialSupportProjection lambda
  apply ContinuousLinearMap.ext
  intro x
  change operator (input x) - sourceSoninProjection lambda
        (operator (input x)) =
      (operator (input x) - radialSupportProjection lambda
          (operator (input x))) +
        (radialSupportProjection lambda
            (radialSupportProjection lambda (operator (input x))) -
          sourceSoninProjection lambda
            (radialSupportProjection lambda (operator (input x))))
  have hradialPoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T (operator (input x))) hradial
  have hsourcePoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T (operator (input x))) hsourceRadial
  simp only [ContinuousLinearMap.comp_apply] at hradialPoint hsourcePoint
  rw [hradialPoint, hsourcePoint]
  abel

/-- Same-owner instance for the selected root applied to the actual source
Sonin inclusion. -/
theorem selectedRoot_sourceSoninLeakage_eq_radialBoundary_add_internalGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        rootConvolution owner ∘L sourceInclusion lambda =
      ((ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L sourceInclusion lambda) +
        ((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L
            sourceInclusion lambda) := by
  exact radialSoninComplement_comp_operator_comp_input_eq_boundary_add_gap
    lambda (sourceInclusion lambda) (rootConvolution owner)

end Dev
end ConnesWeilRH
