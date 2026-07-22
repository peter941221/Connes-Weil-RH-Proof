/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle

/-!
# Alignment of the identity-corrected physical pair

The older corrected physical source pair uses the identity transport inside
its boundary bracket and the literal finite Euler metric coframe on the right.
It is not, by itself, the completed actual-band remainder.

This module identifies its exact operator: the identity bracket collapses to
the three-branch commutator compressed by the outer support on both sides.
The actual remainder is then the sum of the correctly oriented first jet, this
corrected pair, and one explicit outer-complement coframe response.  The
identity is exact and introduces no branchwise estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCorrectedPhysicalPairAlignment

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualBandQuadraticCycle
open CCM24SourceProlateTrace

variable {A : Type*} [Ring A]

/-- If the fixed physical commutator is a compressed signed ledger, then the
identity-transport corrected bracket is exactly that compressed ledger. -/
theorem correctedPhysicalBracket_one_eq_compressed_of_fixed
    (support secondSupport prolate detector ledger : A)
    (hSupport : support * support = support)
    (hfixed : fixedPhysicalCommutator support secondSupport prolate detector =
      -(support * ledger * support)) :
    correctedPhysicalBracket support secondSupport prolate detector 1 =
      support * ledger * support := by
  have hboundary :
      support * (detector * support - support * detector) * support = 0 := by
    calc
      support * (detector * support - support * detector) * support =
          support * detector * (support * support) -
            (support * support) * detector * support := by
        noncomm_ring
      _ = 0 := by rw [hSupport]; simp
  unfold correctedPhysicalBracket compressedPrefix
    CCM24FiniteSTwoSidedRootRecombination.commutator
  simp only [mul_one, hSupport, hboundary, add_zero]
  rw [hfixed]
  calc
    -support * (-(support * ledger * support)) =
        (support * support) * ledger * support := by
      noncomm_ring
    _ = support * ledger * support := by rw [hSupport]

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "AmbientOp" => finiteSCarrier →L[ℂ] finiteSCarrier
local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- On the actual carrier, the identity-corrected bracket is the complete
three-branch commutator with both outer-support compressions retained. -/
theorem sourceCorrectedPhysicalBracket_identity_eq_compressedThreeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    correctedPhysicalBracket (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)
        (ContinuousLinearMap.id ℂ finiteSCarrier) =
      radialSupportProjection lambda ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        radialSupportProjection lambda := by
  change correctedPhysicalBracket (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) (detectorOperator owner) (1 : AmbientOp) =
    radialSupportProjection lambda *
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) *
      radialSupportProjection lambda
  apply correctedPhysicalBracket_one_eq_compressed_of_fixed
  · exact (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  · simpa only [ContinuousLinearMap.mul_def] using
      fixedPhysicalCommutator_eq_neg_compressedThreeBranch
        (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)
        (radialSupportProjection_isStarProjection lambda).isIdempotentElem
        (radialSupportProjection_comp_sourceProlateRemainder lambda)
        (sourceProlateRemainder_comp_radialSupportProjection lambda)

/-- The source inclusion adjoint absorbs the outer radial support. -/
theorem sourceInclusionAdjoint_comp_radialSupportProjection_eq_self
    (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L radialSupportProjection lambda =
      (sourceInclusion lambda)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (radialSupportProjection_comp_sourceInclusion lambda)
  simpa only [ContinuousLinearMap.adjoint_comp,
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]
    using h

/-- The operator owned by the identity-corrected source pair before choosing
any Hilbert bases. -/
noncomputable def sourceIdentityCorrectedPhysicalCoframeResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  (sourceInclusion lambda)† ∘L
    correctedPhysicalBracket (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) (detectorOperator owner)
      (ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
    finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
      finiteEulerGramInv lambda family

/-- The outer-complement coframe term omitted by the identity-corrected pair. -/
noncomputable def sourceOuterComplementThreeBranchResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  (sourceInclusion lambda)† ∘L
    cc20ThreeBranchCommutator (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
    (ContinuousLinearMap.id ℂ finiteSCarrier -
      radialSupportProjection lambda) ∘L
    finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
      finiteEulerGramInv lambda family

/-- Readback of the identity-corrected response after absorbing its redundant
left outer-support projection. -/
theorem sourceIdentityCorrectedPhysicalCoframeResponse_eq_compressedThreeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceIdentityCorrectedPhysicalCoframeResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        radialSupportProjection lambda ∘L finiteEulerAmbientGram family ∘L
        sourceInclusion lambda ∘L finiteEulerGramInv lambda family := by
  rw [sourceIdentityCorrectedPhysicalCoframeResponse,
    sourceCorrectedPhysicalBracket_identity_eq_compressedThreeBranch]
  apply ContinuousLinearMap.ext
  intro u
  have hleft := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)
          (radialSupportProjection lambda
            (finiteEulerAmbientGram family
              (sourceInclusion lambda (finiteEulerGramInv lambda family u))))))
    (sourceInclusionAdjoint_comp_radialSupportProjection_eq_self lambda)
  simpa only [ContinuousLinearMap.comp_apply] using hleft

/-- The identity-corrected response and its explicit outer complement rebuild
the negative raw endpoint without splitting the three physical branches. -/
theorem sourceIdentityCorrected_add_outerComplement_eq_neg_sourceBand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceIdentityCorrectedPhysicalCoframeResponse owner lambda family +
        sourceOuterComplementThreeBranchResponse owner lambda family =
      -sourceBandGramResponse owner lambda family := by
  rw [sourceIdentityCorrectedPhysicalCoframeResponse_eq_compressedThreeBranch,
    sourceBandGramResponse_eq_neg_threeBranch]
  apply ContinuousLinearMap.ext
  intro u
  simp only [neg_neg]
  let v : finiteSCarrier := finiteEulerAmbientGram family
    (sourceInclusion lambda (finiteEulerGramInv lambda family u))
  change ContinuousLinearMap.adjoint (sourceInclusion lambda)
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)
          (radialSupportProjection lambda v)) +
      ContinuousLinearMap.adjoint (sourceInclusion lambda)
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)
          (v - radialSupportProjection lambda v)) =
      ContinuousLinearMap.adjoint (sourceInclusion lambda)
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) v)
  rw [map_sub, map_sub]
  abel

/-- Exact actual-remainder assembly.  The old corrected source pair is one
piece; the correctly oriented first jet and the outer-complement coframe term
are both mandatory. -/
theorem sourceActualBandFiniteEulerRemainderResponse_eq_correctedAssembly
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerRemainderResponse owner lambda family =
      actualBandFirstJetCycledResponse owner lambda family +
        sourceIdentityCorrectedPhysicalCoframeResponse owner lambda family +
        sourceOuterComplementThreeBranchResponse owner lambda family := by
  calc
    sourceActualBandFiniteEulerRemainderResponse owner lambda family =
        actualBandFirstJetCycledResponse owner lambda family -
          sourceBandGramResponse owner lambda family := by
      rw [sourceActualBandFiniteEulerRemainderResponse,
        sourceActualBandFiniteEulerSoninResponse_eq_firstJetCycle]
    _ = actualBandFirstJetCycledResponse owner lambda family +
        (-sourceBandGramResponse owner lambda family) := sub_eq_add_neg _ _
    _ = actualBandFirstJetCycledResponse owner lambda family +
        (sourceIdentityCorrectedPhysicalCoframeResponse owner lambda family +
          sourceOuterComplementThreeBranchResponse owner lambda family) := by
      rw [sourceIdentityCorrected_add_outerComplement_eq_neg_sourceBand]
    _ = actualBandFirstJetCycledResponse owner lambda family +
        sourceIdentityCorrectedPhysicalCoframeResponse owner lambda family +
        sourceOuterComplementThreeBranchResponse owner lambda family := by
      abel

/-- The previously unused source pair owns exactly the named identity-corrected
coframe response. -/
theorem sourceCorrectedPhysicalSourcePairData_traceProduct_eq_identityResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ σ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (correctedBoundaryBasis : HilbertBasis σ ℂ (correctedBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceCorrectedPhysicalSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      correctedBoundaryBasis sourceBasis hfactor).traceProduct =
        sourceIdentityCorrectedPhysicalCoframeResponse owner lambda family := by
  rw [sourceCorrectedPhysicalSourcePairData_traceProduct_eq]
  rfl

end CCM24FiniteSCorrectedPhysicalPairAlignment
end CCM25Concrete
end Source
end ConnesWeilRH
