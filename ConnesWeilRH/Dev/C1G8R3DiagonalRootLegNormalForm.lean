/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffSurvivorBoundaryTraceLimit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace

/-!
# Detector-root normal form for the G8 diagonal channels

Each finite-cutoff diagonal channel is the positive square of the selected
detector root applied to the corresponding coframe and source cutoff. Its
ordinary trace is exactly the same-basis column-energy sum. This isolates the
uniform Hilbert--Schmidt limit needed for the two diagonal G8 channels.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance diagonalRootSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The selected detector root after a diagonal G8 coframe and the actual
source-compressed finite-window cutoff. -/
noncomputable def g8MetricCutoffDetectorRootLeg
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (n : ℕ)
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L leg ∘L (sourceInclusion lambda).adjoint ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left

/-- A diagonal metric channel is the exact positive composition of its
selected detector-root leg. -/
theorem g8MetricCutoffDiagonalChannel_eq_rootLeg_square
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (n : ℕ)
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n leg leg =
      (g8MetricCutoffDetectorRootLeg owner lambda family globalBasis sourceBasis
        n leg).adjoint ∘L
        g8MetricCutoffDetectorRootLeg owner lambda family globalBasis sourceBasis
          n leg := by
  unfold g8MetricCutoffChannel g8MetricCutoffDetectorRootLeg
  rw [detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]

/-- The ordinary trace of a finite-cutoff diagonal channel is the detector-root
column-energy sum on the caller's same source basis. -/
theorem ordinaryTraceAlong_g8MetricCutoffDiagonal_eq_rootLeg_energy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (n : ℕ)
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n leg leg) =
      ((∑' i, ‖g8MetricCutoffDetectorRootLeg owner lambda family globalBasis
        sourceBasis n leg (sourceBasis i)‖ ^ 2 : ℝ) : ℂ) := by
  let rootLeg := g8MetricCutoffDetectorRootLeg owner lambda family globalBasis
    sourceBasis n leg
  have hfactor :
      IsTraceClassAlong sourceBasis (rootLeg.adjoint ∘L rootLeg) := by
    rw [← g8MetricCutoffDiagonalChannel_eq_rootLeg_square owner lambda family
      globalBasis sourceBasis n leg]
    exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n leg leg
  have hsum := PositiveTrace.summable_normSq_of_isTraceClassAlong_adjoint_comp_self
    sourceBasis rootLeg hfactor
  rw [g8MetricCutoffDiagonalChannel_eq_rootLeg_square owner lambda family
    globalBasis sourceBasis n leg]
  rw [ordinaryTraceAlong]
  simp_rw [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_pow] using
    (Complex.ofRealCLM.map_tsum hsum).symm

end Dev
end ConnesWeilRH
