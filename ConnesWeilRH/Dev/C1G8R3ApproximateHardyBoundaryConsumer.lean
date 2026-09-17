/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ApproximateHardySupportConsumer

/-!
# Approximate Hardy-support boundary consumer

This assembles the approximate Hardy-support gap leg with the already
available radial leg for the actual G8 visible boundary coframe.  The exact
wide-Hardy identity is retained for the radial leg; only the gap leg is
replaced by the explicit Hardy-tail square sum.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedWeilSquare
open Source.C1G8P1MetricChannels
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable local instance approximateHardyBoundaryConsumerCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 20000000 in
theorem g8MetricVisibleBoundary_root_energy_summable_of_approximateHardy_tail
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hleg : ∀ output ∈ finiteEulerMetricCoframeBoundaryMaps lambda family,
      ∃ (M : finiteSCarrier →L[ℂ] finiteSCarrier)
          (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
          (s : ℝ),
        output = M ∘L sourceInclusion lambda ∘L N ∧
        0 ≤ s ∧
        Summable (fun i : ρ =>
          ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L M ∘L
            sourceInclusion lambda) (N (sourceBasis i))‖ ^ 2) ∧
        radialSupportProjection (wideRadialScale lambda s) ∘L M ∘L
            sourceInclusion lambda = M ∘L sourceInclusion lambda ∧
        Summable (fun i : ρ =>
          ‖(((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
              radialSupportProjection lambda ∘L rootConvolution owner) ∘L
            (archimedeanHardyTitchmarshOperator ∘L
              (ContinuousLinearMap.id ℂ finiteSCarrier -
                radialSupportProjection (wideRadialScale lambda s)) ∘L
              archimedeanHardyTitchmarshOperator ∘L
              M ∘L sourceInclusion lambda) ∘L N) (sourceBasis i)‖ ^ 2)) :
    Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L
          g8MetricVisibleBoundaryCoframe lambda family) (sourceBasis i)‖ ^ 2 := by
  refine g8MetricVisibleBoundary_root_energy_summable_of_legs owner lambda
    family sourceBasis (fun output hmem => ?_)
  obtain ⟨M, N, s, hout, hs, hin, hwide, htail⟩ := hleg output hmem
  refine ⟨M, N, hout, hin, ?_, ?_⟩
  · exact compositeRadialLeg_sourceBasis_normSq_summable owner lambda s hs M N
      sourceBasis hwide
  · exact compositeGapLeg_sourceColumn_normSq_summable_of_approximateHardyRadialTail
      owner lambda s hs (M ∘L sourceInclusion lambda) N sourceBasis htail

end Dev
end ConnesWeilRH
