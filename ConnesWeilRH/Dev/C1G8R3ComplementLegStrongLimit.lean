/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffCrossTraceLimit

/-!
# Strong limit for the G8 source-projection complement leg

The literal source cutoff leg splits into its source-compressed part and its
orthogonal source-projection defect.  This leaf identifies the defect's
pointwise strong limit on the same source carrier.  No trace convergence or
vanishing estimate is asserted.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.Dev.C1PositiveTraceCutoffAdapter
open Source.Dev.C1PositiveTraceWindowProducer
open Source.Dev.C1Stage3ProjectionWindow
open Source.C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance g8ComplementSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The strong limit of the actual source-projection complement leg. -/
noncomputable def g8GlobalConvolutionSourceComplementLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L
      sourceInclusion lambda -
    sourceInclusion lambda ∘L
      g8SourceCompressedGlobalConvolution lambda owner.sourceTest

/-- The literal cutoff complement is the ambient physical cutoff after source
inclusion, minus its source-compressed part. -/
theorem g8SourceCutoffComplementLeg_eq_cutoffDifference
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : ℕ) :
    g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n =
      fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L
        sourceInclusion lambda -
      sourceInclusion lambda ∘L
        g8SourceCompressedPhysicalCutoff owner lambda n := by
  simp [g8SourceCutoffComplementLeg, g8SourceCompressedPhysicalCutoff,
    g8SourceCutoffPairData, g8CutoffPairData,
    Source.Dev.C1Stage3ProjectionWindow.kernelSandwichPairData]

/-- The source-projection complement converges strongly to the part of the
global detector convolution outside the selected source image. -/
theorem tendsto_g8SourceCutoffComplementLeg_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι ρ : Type*}
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (x : sourceSoninCarrier lambda) :
    Tendsto
      (fun n : ℕ =>
        g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n x)
      atTop (𝓝 (g8GlobalConvolutionSourceComplementLeg owner lambda x)) := by
  have hambient := tendsto_fullBoundaryPositiveOperator_cutoff_apply
    owner.sourceTest (sourceInclusion lambda x)
  have hcompressed := tendsto_g8SourceCompressedPhysicalCutoff_apply
    owner lambda x
  have hcompressedMap :=
    (sourceInclusion lambda).continuous.tendsto _ |>.comp hcompressed
  have hlimit := hambient.sub hcompressedMap
  have hsequence :
      (fun n : ℕ =>
        g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n x) =
      (fun n =>
        fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
            (sourceInclusion lambda x) -
          sourceInclusion lambda
            (g8SourceCompressedPhysicalCutoff owner lambda n x)) := by
    funext n
    rw [g8SourceCutoffComplementLeg_eq_cutoffDifference]
    rfl
  rw [hsequence]
  simpa [g8GlobalConvolutionSourceComplementLeg,
    g8SourceCompressedGlobalConvolution] using hlimit

end Dev
end ConnesWeilRH
