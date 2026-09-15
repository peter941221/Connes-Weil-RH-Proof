/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1VisibleBoundaryEnergy
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier

/-!
# The source-prolate input in the G8 boundary energy estimate is zero

The prolate factor is supported on the source quotient band, while the source
inclusion lands in the orthogonal Sonin carrier. Its pullback through the
source inclusion therefore vanishes. This audits the exact input used by the
existing G8 visible-boundary energy estimate; it does not estimate the actual
root/coframe columns.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The source-prolate square-root factor vanishes on the included
source-Sonin carrier. -/
theorem sourceProlateHilbertSchmidtFactor_comp_sourceInclusion_eq_zero
    (lambda : CCM24SoninScale) :
    sourceProlateHilbertSchmidtFactor lambda ∘L sourceInclusion lambda = 0 := by
  calc
    sourceProlateHilbertSchmidtFactor lambda ∘L sourceInclusion lambda =
        sourceFourierSupportProjection lambda ∘L
          sourceBandProjection lambda ∘L sourceInclusion lambda := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply,
        sourceProlateHilbertSchmidtFactor, sourceBandProjection]
    _ = sourceFourierSupportProjection lambda ∘L 0 := by
      rw [sourceBandProjection_comp_sourceInclusion_eq_zero]
    _ = 0 := by simp

/-- Pulling the source-prolate remainder back to the source carrier gives
zero, so postcomposing with the visible-boundary coframe remains zero. -/
theorem g8MetricVisibleBoundaryCoframe_comp_sourceProlatePullback_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8MetricVisibleBoundaryCoframe lambda family ∘L
      ((sourceInclusion lambda)† ∘L
        sourceProlateHilbertSchmidtFactor lambda ∘L sourceInclusion lambda) =
      0 := by
  rw [sourceProlateHilbertSchmidtFactor_comp_sourceInclusion_eq_zero]
  simp

end Dev
end ConnesWeilRH
