/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphPhysicalTransportReadback
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade

/-!
# Actual Schur-cascade readback of the physical graph residual

Proof 524 identifies the physical Euler transport of one concrete projected
graph frame.  The actual Schur cascade stores that projected transport as its
one-step ambient map.  This module makes that identification explicit and
rewrites the unprojected physical graph response as the actual step transport
plus the same physical support residual.

No post-Q vanishing, family-uniform estimate, sign, or RH conclusion is
introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphPhysicalCascadeReadback

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurGraphSupportDefect
open CCM24FiniteSActualSchurGraphSupportDefectReadback
open CCM24FiniteSActualSchurGraphPhysicalTransportReadback
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaSchur

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def suffixStepPrimeEulerInput
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    PrimeEulerProjectedJuliaInput :=
  parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p

theorem suffixActualSchurFrameStep_transport_eq_projectedGraphPhysicalTransport
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (suffixActualSchurFrameStep lambda stepData p S).transport =
      normalizedPrimeEulerFrameTransport p ∘L
        canonicalProjectedGraphFrame (suffixStepPrimeEulerInput lambda p S) := by
  change (suffixStepPrimeEulerInput lambda p S).normalizedSchurFrame = _
  simpa only [suffixStepPrimeEulerInput,
    parameterizedPrimeEulerProjectedJuliaInput_prime] using
    (normalizedPrimeEulerFrameTransport_comp_projectedGraphFrame
      (suffixStepPrimeEulerInput lambda p S)).symm

theorem suffixActualSchurFrameStep_fullGraphPhysicalTransport_eq_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L
        canonicalFullGraphFrame (suffixStepPrimeEulerInput lambda p S) =
      (suffixActualSchurFrameStep lambda stepData p S).transport +
        normalizedCanonicalGraphPhysicalResidual
          (suffixStepPrimeEulerInput lambda p S) := by
  calc
    normalizedPrimeEulerFrameTransport p ∘L
          canonicalFullGraphFrame (suffixStepPrimeEulerInput lambda p S) =
        (suffixStepPrimeEulerInput lambda p S).normalizedSchurFrame +
          normalizedCanonicalGraphPhysicalResidual
            (suffixStepPrimeEulerInput lambda p S) := by
      simpa only [suffixStepPrimeEulerInput,
        parameterizedPrimeEulerProjectedJuliaInput_prime] using
        (normalizedPrimeEulerFrameTransport_comp_fullGraphFrame_eq_normalizedSchurFrame_add_residual
          (suffixStepPrimeEulerInput lambda p S))
    _ = (suffixActualSchurFrameStep lambda stepData p S).transport +
          normalizedCanonicalGraphPhysicalResidual
            (suffixStepPrimeEulerInput lambda p S) := by
      rw [suffixActualSchurFrameStep_transport_eq_projectedGraphPhysicalTransport
        lambda stepData p S]
      simpa only [suffixStepPrimeEulerInput,
        parameterizedPrimeEulerProjectedJuliaInput_prime] using
        congrArg
          (fun z => z + normalizedCanonicalGraphPhysicalResidual
            (suffixStepPrimeEulerInput lambda p S))
          (normalizedPrimeEulerFrameTransport_comp_projectedGraphFrame
            (suffixStepPrimeEulerInput lambda p S)).symm

theorem suffixActualSchurFrameStep_fullGraphPhysicalTransport_sub_transport_eq_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L
        canonicalFullGraphFrame (suffixStepPrimeEulerInput lambda p S) -
        (suffixActualSchurFrameStep lambda stepData p S).transport =
      normalizedCanonicalGraphPhysicalResidual
        (suffixStepPrimeEulerInput lambda p S) := by
  rw [suffixActualSchurFrameStep_fullGraphPhysicalTransport_eq_add_residual
    lambda stepData p S]
  abel

theorem suffixActualSchurFrameStep_fullGraphPhysicalTransport_sub_transport_norm_le_supportDefect
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ‖normalizedPrimeEulerFrameTransport p ∘L
        canonicalFullGraphFrame (suffixStepPrimeEulerInput lambda p S) -
        (suffixActualSchurFrameStep lambda stepData p S).transport‖ ≤
      ‖canonicalGraphSupportDefect (suffixStepPrimeEulerInput lambda p S)‖ := by
  rw [suffixActualSchurFrameStep_fullGraphPhysicalTransport_sub_transport_eq_residual
    lambda stepData p S]
  exact normalizedCanonicalGraphPhysicalResidual_norm_le_supportDefect
    (suffixStepPrimeEulerInput lambda p S)

end CCM24FiniteSActualSchurGraphPhysicalCascadeReadback
end CCM25Concrete
end Source
end ConnesWeilRH
