/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3CompositeBoundaryEnergy

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24FiniteSActualBandFirstJetTrace
open Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
open Source.CCM25Concrete.CCM24FiniteSCausalSupport
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open Source.CCM25Concrete.AntiresonantFrameLossRadialReduction
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20Concrete.ELambdaProjector
open scoped ENNReal InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier

set_option maxHeartbeats 20000000 in
/-- Joint S3/B4 consumer: a Hardy-sub-identity estimate for the source
projection commutator, together with the existing prolate factor, supplies
the B4 internal-gap square-sum.  This is the shared cancellation interface;
the Hardy-sub-identity estimate itself remains the analytic producer. -/
theorem sourceSoninCommutator_sourceBasis_normSq_summable_of_hardySubId_factor_explicit
    (lambda : CCM24SoninScale)
    (M : Carrier →L[ℂ] Carrier)
    (D : finiteSCarrier →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ Carrier)
    (hfactor : Summable fun i : ν =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hHardy : Summable fun i : ρ =>
      ‖(D ∘L (radialSupportProjection lambda ∘L
          sourceFourierSupportProjection lambda ∘L
          radialSupportProjection lambda ∘L M - M) ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ =>
      ‖(D ∘L cc20Commutator (sourceSoninProjection lambda) M ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2 := by
  exact @sourceSoninCommutator_sourceBasis_normSq_summable_of_hardySubId_factor
    lambda ν ρ globalBasis sourceBasis M D N hfactor hHardy

end ConnesWeilRH.Dev
