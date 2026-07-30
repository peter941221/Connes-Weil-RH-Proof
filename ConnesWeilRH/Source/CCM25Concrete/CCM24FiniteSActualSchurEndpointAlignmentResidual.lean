/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistoryMismatch
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization

/-!
# Actual Schur endpoint alignment residual

The raw physical ledger is indexed by a literal suffix list, while the
physical/actual-Schur endpoint residual is indexed by a finite prime-power
family.  This module proves the visible-prime carrier bridge and keeps the
remaining endpoint mismatch as one signed residual.

No residual is set to zero, bounded, signed, or Douglas-factored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurEndpointAlignmentResidual

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurTelescoping
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSCompletedPhysicalHistoryMismatch
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCoframeResponse
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSInverseMetric
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Family/list carrier bridges -/

theorem suffixActualBandForwardCoframe_visiblePrimes_eq_sourceActualBandForwardCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandForwardCoframe lambda family.visiblePrimes =
      sourceActualBandForwardCoframe lambda family := by
  have hphysical :
      normalizedFiniteEulerInverse family =
        normalizedFiniteEulerInverseList family.visiblePrimes := by
    rw [normalizedFiniteEulerInverse_eq_causalAverage,
      finiteEulerCausalAverage_eq_normalizedInverse]
  unfold suffixActualBandForwardCoframe sourceActualBandForwardCoframe
  rw [hphysical]

theorem suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandMetricCoframe lambda family.visiblePrimes =
      finiteEulerMetricCoframe lambda family := by
  unfold suffixActualBandMetricCoframe finiteEulerMetricCoframe
    suffixActualBandAmbientGram suffixActualBandTransportOperator
    CCM24FiniteSGramResponse.finiteEulerAmbientGram suffixActualBandGramInv
  rw [parameterizedSoninGramInv_one_eq_finiteEulerGramInv]

theorem suffixActualBandForwardEndpointCoframe_visiblePrimes_eq_sourceActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandForwardEndpointCoframe lambda family.visiblePrimes =
      sourceActualBandForwardEndpointCoframe lambda family := by
  unfold suffixActualBandForwardEndpointCoframe
    sourceActualBandForwardEndpointCoframe
  rw [suffixActualBandForwardCoframe_visiblePrimes_eq_sourceActualBandForwardCoframe,
    suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe]

theorem suffixActualSchurForwardEndpointCoframe_visiblePrimes_eq_sourceActualBandForwardSchurEndpointCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    suffixActualSchurForwardEndpointCoframe lambda stepData
        family.visiblePrimes =
      sourceActualBandForwardSchurEndpointCoframe lambda stepData family := by
  unfold suffixActualSchurForwardEndpointCoframe
    sourceActualBandForwardSchurEndpointCoframe
  rw [suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe]

/-! ## The physical endpoint readback -/

theorem sourceActualBandForwardEndpointCoframe_eq_namedSchurForwardEndpoint_add_transportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      sourceActualBandForwardSchurEndpointCoframe lambda stepData family +
        sourceActualBandForwardTransportResidual lambda stepData
          family.visiblePrimes := by
  exact
    sourceActualBandForwardEndpointCoframe_eq_schurForwardEndpoint_add_residual
      lambda stepData family

theorem sourceActualBandForwardEndpointCoframe_eq_suffixNamedSchurEndpoint_add_transportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      suffixActualSchurForwardEndpointCoframe lambda stepData
          family.visiblePrimes +
        sourceActualBandForwardTransportResidual lambda stepData
          family.visiblePrimes := by
  rw [sourceActualBandForwardEndpointCoframe_eq_namedSchurForwardEndpoint_add_transportResidual
    lambda stepData family,
    ← suffixActualSchurForwardEndpointCoframe_visiblePrimes_eq_sourceActualBandForwardSchurEndpointCoframe
      lambda stepData family]

/-! ## The actual-Schur endpoint alignment residual -/

/-- The difference between the physical transport residual and the
physical/actual-Schur endpoint residual. -/
noncomputable def suffixActualSchurEndpointAlignmentResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardTransportResidual lambda stepData family.visiblePrimes -
    suffixActualSchurEndpointResidual lambda stepData family

theorem suffixActualSchurEndpointCoframe_eq_suffixNamedSchurEndpoint_add_alignmentResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    suffixActualSchurEndpointCoframe lambda stepData family =
      suffixActualSchurForwardEndpointCoframe lambda stepData
          family.visiblePrimes +
        suffixActualSchurEndpointAlignmentResidual lambda stepData family := by
  rw [suffixActualSchurEndpointAlignmentResidual]
  calc
    suffixActualSchurEndpointCoframe lambda stepData family =
        sourceActualBandForwardEndpointCoframe lambda family -
          suffixActualSchurEndpointResidual lambda stepData family := by
      apply ContinuousLinearMap.ext
      intro x
      have hpoint := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          operator x)
        (sourceActualBandForwardEndpointCoframe_eq_actualSchurEndpoint_add_residual
          lambda stepData family)
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
        at hpoint ⊢
      rw [hpoint]
      abel
    _ = (sourceActualBandForwardSchurEndpointCoframe lambda stepData family +
          sourceActualBandForwardTransportResidual lambda stepData
            family.visiblePrimes) -
          suffixActualSchurEndpointResidual lambda stepData family := by
      rw [sourceActualBandForwardEndpointCoframe_eq_namedSchurForwardEndpoint_add_transportResidual
        lambda stepData family]
    _ = suffixActualSchurForwardEndpointCoframe lambda stepData
          family.visiblePrimes +
          (sourceActualBandForwardTransportResidual lambda stepData
              family.visiblePrimes -
            suffixActualSchurEndpointResidual lambda stepData family) := by
      rw [suffixActualSchurForwardEndpointCoframe_visiblePrimes_eq_sourceActualBandForwardSchurEndpointCoframe
        lambda stepData family]
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
      abel

end CCM24FiniteSActualSchurEndpointAlignmentResidual
end CCM25Concrete
end Source
end ConnesWeilRH
