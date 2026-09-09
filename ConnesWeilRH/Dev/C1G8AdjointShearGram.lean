import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction

/-!
# G8 adjoint-shear Gram compression

This leaf records the first owner-level algebraic identity for the live G8
candidate.  The adjoint shear is placed on the input side, so the source
compression retains the physical oblique-shear response.  No trace estimate,
`qw` readback, sign theorem, or RH conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8AdjointShearGram

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
open CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM25Concrete.CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSPhysicalLeakage
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

local notation "AmbientOp" =>
  finiteSCarrier →L[ℂ] finiteSCarrier

/-- The G8 positive Gram kernel before any trace is taken. -/
noncomputable def g8AdjointShearGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : AmbientOp :=
  (ContinuousLinearMap.id ℂ finiteSCarrier +
      (finiteEulerPulledObliqueShear lambda family)†)† ∘L
    detectorOperator owner ∘L
      (ContinuousLinearMap.id ℂ finiteSCarrier +
        (finiteEulerPulledObliqueShear lambda family)†)

/-- Compression of G8 to the healthy source owner keeps all four Gram terms.
The second term is the active oblique-shear response orientation. -/
theorem sourceCompression_g8AdjointShearGram_eq_fourTerms
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          sourceInclusion lambda =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          (finiteEulerPulledObliqueShear lambda family)† ∘L
            sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L
              (finiteEulerPulledObliqueShear lambda family)† ∘L
                sourceInclusion lambda := by
  let J := sourceInclusion lambda
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  have hadjoint_add (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  change J† ∘L ((ContinuousLinearMap.id ℂ finiteSCarrier + N†)† ∘L W ∘L
      (ContinuousLinearMap.id ℂ finiteSCarrier + N†)) ∘L J = _
  rw [hadjoint_add, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add]
  abel

/-- The second Gram term is exactly the already-owned oblique-shear response,
with no trace cycle or adjoint rearrangement. -/
theorem sourceCompression_g8AdjointShearGram_cross_eq_targetResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        finiteEulerPulledObliqueShear lambda family ∘L
      detectorOperator owner ∘L sourceInclusion lambda =
      finiteEulerTargetCommutatorResponse owner lambda family := by
  change finiteEulerPulledObliqueShearResponse owner lambda family = _
  exact (finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear
    owner lambda family).symm

end
end C1G8AdjointShearGram
end Source
end ConnesWeilRH
