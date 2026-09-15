/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3DiagonalRootEnergyLimitConstraint
import ConnesWeilRH.Dev.C1G8R3ActualCutoffSurvivorBoundaryTraceLimit

/-!
# Conditional total trace limit for the actual G8 metric cutoff

The literal four-channel metric trace has a same-owner limit if the two
diagonal detector-root legs have square-summable columns on the source basis.
The mixed survivor/boundary pair already has an unconditional trace limit.
This records the exact remaining energy hypotheses without claiming them.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricBoundary
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance totalMetricSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
/-- The actual four-channel G8 physical metric trace converges provided the
two same-owner diagonal detector-root columns are square-summable on the
source basis. The mixed survivor/boundary pair needs no additional energy
 hypothesis. -/
theorem tendsto_ordinaryTraceAlong_g8PhysicalMetricCutoff_of_diagonal_root_legs_summable
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hSurvivor : Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L g8MetricSurvivorCoframe lambda family)
        (sourceBasis i)‖ ^ 2)
    (hBoundary : Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L g8MetricVisibleBoundaryCoframe lambda family)
        (sourceBasis i)‖ ^ 2) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n))
      atTop
      (𝓝
        (ordinaryTraceAlong sourceBasis
            ((g8MetricGlobalDetectorRootLeg owner lambda
              (g8MetricSurvivorCoframe lambda family)).adjoint ∘L
                g8MetricGlobalDetectorRootLeg owner lambda
                  (g8MetricSurvivorCoframe lambda family)) +
          ((2 * (ordinaryTraceAlong sourceBasis
            ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
              (g8MetricSurvivorCoframe lambda family).adjoint ∘L
                detectorOperator owner ∘L
                  g8MetricVisibleBoundaryCoframe lambda family ∘L
                    g8SourceCompressedGlobalConvolution lambda owner.sourceTest)).re : ℝ) : ℂ) +
          ordinaryTraceAlong sourceBasis
            ((g8MetricGlobalDetectorRootLeg owner lambda
              (g8MetricVisibleBoundaryCoframe lambda family)).adjoint ∘L
                g8MetricGlobalDetectorRootLeg owner lambda
                  (g8MetricVisibleBoundaryCoframe lambda family)))) := by
  have hSS :=
    tendsto_ordinaryTraceAlong_g8MetricCutoffDiagonal_of_rootLeg_summable
      owner lambda family globalBasis sourceBasis
      (g8MetricSurvivorCoframe lambda family) hSurvivor
  have hBB :=
    tendsto_ordinaryTraceAlong_g8MetricCutoffDiagonal_of_rootLeg_summable
      owner lambda family globalBasis sourceBasis
      (g8MetricVisibleBoundaryCoframe lambda family) hBoundary
  have hSB :=
    tendsto_ordinaryTraceAlong_g8MetricPairedSurvivorBoundary_actualCutoff
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis
  have hfour := (hSS.add hSB).add hBB
  have htracePointwise (n : ℕ) :
      ordinaryTraceAlong sourceBasis
          (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n) =
        ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricSurvivorCoframe lambda family)
              (g8MetricSurvivorCoframe lambda family)) +
          ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricSurvivorCoframe lambda family)
              (g8MetricVisibleBoundaryCoframe lambda family) +
             g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricVisibleBoundaryCoframe lambda family)
              (g8MetricSurvivorCoframe lambda family)) +
          ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricVisibleBoundaryCoframe lambda family)
              (g8MetricVisibleBoundaryCoframe lambda family)) := by
    rw [ordinaryTraceAlong_g8PhysicalMetricCutoffOperator_eq_fourChannels]
    have hSBtc := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
        (g8MetricVisibleBoundaryCoframe lambda family)
    have hBStc := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
        (g8MetricSurvivorCoframe lambda family)
    calc
      _ = ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricSurvivorCoframe lambda family)
              (g8MetricSurvivorCoframe lambda family)) +
          (ordinaryTraceAlong sourceBasis
              (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
                (g8MetricSurvivorCoframe lambda family)
                (g8MetricVisibleBoundaryCoframe lambda family)) +
            ordinaryTraceAlong sourceBasis
              (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
                (g8MetricVisibleBoundaryCoframe lambda family)
                (g8MetricSurvivorCoframe lambda family))) +
          ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricVisibleBoundaryCoframe lambda family)
              (g8MetricVisibleBoundaryCoframe lambda family)) := by ring
      _ = _ := by
        rw [ordinaryTraceAlong_add sourceBasis _ _ hSBtc hBStc]
  have htraceEq :
      (fun n => ordinaryTraceAlong sourceBasis
        (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n)) =
      (fun n => ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricSurvivorCoframe lambda family)
            (g8MetricSurvivorCoframe lambda family)) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricSurvivorCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family) +
           g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricSurvivorCoframe lambda family)) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family))) := by
    funext n
    exact htracePointwise n
  rw [htraceEq]
  simpa only [ordinaryTraceAlong_g8MetricCutoffDiagonal_eq_rootLeg_energy] using hfour

end Dev
end ConnesWeilRH
