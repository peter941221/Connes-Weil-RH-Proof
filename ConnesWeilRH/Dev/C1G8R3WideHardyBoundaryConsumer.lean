/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3CompositeBoundaryEnergy

/-!
# B4 support-certificate consumer

This is the final B4 bookkeeping consumer.  It replaces the two diagonal
square-sum premises by the corresponding wide-radial and Hardy-wide-radial
support identities on the same factorization owner.  The analytic support
identities are deliberately left as hypotheses; this file proves that no
additional projection, triangle, or trace premise is hidden downstream.
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

noncomputable local instance wideHardyBoundaryConsumerCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
theorem g8MetricVisibleBoundary_root_energy_summable_of_wideHardy_support
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
        radialSupportProjection (wideRadialScale lambda s) ∘L
            archimedeanHardyTitchmarshOperator ∘L M ∘L
            sourceInclusion lambda =
          archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda) :
    Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L
          g8MetricVisibleBoundaryCoframe lambda family) (sourceBasis i)‖ ^ 2 := by
  refine g8MetricVisibleBoundary_root_energy_summable_of_legs owner lambda
    family sourceBasis (fun output hmem => ?_)
  obtain ⟨M, N, s, hout, hs, hin, hwide, hwideHT⟩ := hleg output hmem
  refine ⟨M, N, hout, hin, ?_, ?_⟩
  · exact compositeRadialLeg_sourceBasis_normSq_summable owner lambda s hs M N
      sourceBasis hwide
  · exact compositeGapLeg_sourceBasis_normSq_summable owner lambda s hs M N
      sourceBasis hwideHT

end Dev
end ConnesWeilRH
