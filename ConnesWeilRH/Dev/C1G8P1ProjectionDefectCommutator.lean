import ConnesWeilRH.Dev.C1G8P1ProjectionDefectRealLedger

/-!
# G8 P1 projection-defect commutator localization

The source-projection complement is killed by the inclusion adjoint.  Hence
the remaining signed projection-defect cross channel is precisely the
off-diagonal source-projection commutator of the positive G8 Gram.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1ProjectionDefectCommutator

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The literal cutoff complement lies in the kernel of the source inclusion
adjoint. -/
theorem sourceInclusion_adjoint_comp_g8SourceCutoffComplementLeg_eq_zero
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (sourceInclusion lambda)† ∘L
      g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n = 0 := by
  unfold g8SourceCutoffComplementLeg
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub,
    ContinuousLinearMap.zero_apply]
  have hJJ := congrFun (congrArg DFunLike.coe
    (sourceInclusion_adjoint_comp_self lambda))
    (((sourceInclusion lambda)†)
      ((g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left u))
  have hJJ_apply : ((sourceInclusion lambda)†)
      (sourceInclusion lambda
        (((sourceInclusion lambda)†)
          ((g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left u))) =
      ((sourceInclusion lambda)†)
        ((g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left u) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hJJ
  rw [hJJ_apply]
  exact sub_self _

/-- The source projection kills the literal cutoff complement. -/
theorem sourceSoninProjection_comp_g8SourceCutoffComplementLeg_eq_zero
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninProjection lambda ∘L
      g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n = 0 := by
  rw [← sourceInclusion_comp_adjoint]
  rw [ContinuousLinearMap.comp_assoc]
  rw [sourceInclusion_adjoint_comp_g8SourceCutoffComplementLeg_eq_zero]
  rfl

/- The source--Gram commutator identity expands several same-owner operators. -/
set_option maxHeartbeats 1000000 in
-- The sole signed projection-defect cross operator is the source--Gram
-- off-diagonal block, expressed as the source-projection commutator applied
-- to the complement leg.
theorem g8ProjectionDefectCross_eq_sourceProjection_commutator
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
     let J := sourceInclusion lambda
     let C := J† ∘L A
     let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
     let G := g8AdjointShearGram owner lambda family
     C† ∘L J† ∘L G ∘L D) =
    (let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
     let J := sourceInclusion lambda
     let C := J† ∘L A
     let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
     let G := g8AdjointShearGram owner lambda family
     let P := sourceSoninProjection lambda
     C† ∘L J† ∘L (P ∘L G - G ∘L P) ∘L D) := by
  dsimp only
  have hPD := sourceSoninProjection_comp_g8SourceCutoffComplementLeg_eq_zero
    owner lambda family globalBasis sourceBasis n
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  have hPDu := congrFun (congrArg DFunLike.coe hPD) u
  change sourceSoninProjection lambda
      (g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n u) = 0 at hPDu
  have hJP := congrFun (congrArg DFunLike.coe
    (sourceInclusionAdjoint_comp_sourceProjection lambda))
    (g8AdjointShearGram owner lambda family
      (g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n u))
  have hJP_apply : ((sourceInclusion lambda)†)
      (sourceSoninProjection lambda
        (g8AdjointShearGram owner lambda family
          (g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n u))) =
      ((sourceInclusion lambda)†)
        (g8AdjointShearGram owner lambda family
          (g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n u)) := by
    simpa only [ContinuousLinearMap.comp_apply] using hJP
  rw [hJP_apply, hPDu]
  simp

end
end C1G8P1ProjectionDefectCommutator
end Source
end ConnesWeilRH
