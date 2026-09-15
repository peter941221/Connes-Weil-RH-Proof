/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1BoundaryRootEnergyReduction
import ConnesWeilRH.Dev.C1G8R3PhysicalMetricCutoffTotalTraceLimit

/-!
# Per-output boundary energies feed the actual G8 trace limit

This consumer replaces the aggregate boundary-energy premise by explicit
same-owner square-summability for each actual finite-prime boundary output.
The survivor leg remains the existing same-basis premise, and the
survivor/boundary mixed trace limit is unchanged.
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
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricBoundary
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance boundaryConsumerSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The actual four-channel G8 trace converges when every true Schur--polar
boundary output has square-summable selected-root columns on the same source
basis. -/
theorem tendsto_ordinaryTraceAlong_g8PhysicalMetricCutoff_of_each_boundary_output_summable
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
    (hBoundaryOutput : ∀ output ∈ finiteEulerMetricCoframeBoundaryMaps lambda family,
      Summable fun i : ρ =>
        ‖(rootConvolution owner ∘L output) (sourceBasis i)‖ ^ 2) :
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
  exact tendsto_ordinaryTraceAlong_g8PhysicalMetricCutoff_of_diagonal_root_legs_summable
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
    boundaryBasis sourceBasis hSurvivor
    (g8MetricVisibleBoundary_root_energy_summable_of_each_output owner lambda family
      sourceBasis hBoundaryOutput)

end Dev
end ConnesWeilRH
