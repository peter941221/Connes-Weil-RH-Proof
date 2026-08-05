/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInverseMetric
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalSupport

/-!
# Forward actual-band coframe is the complete off-Sonin normalized inverse

For `J = sourceInclusion`, `R = radialSupportProjection`,
`Q = sourceSoninProjection`, `B = R - Q`, and `N = normalizedFiniteEulerInverse`:

    forward = B∘N∘J = (I - Q) ∘ (N ∘ J).

The two in-library radial facts that make this true are
`R∘J = J` (the source inclusion is radial) and the fact that the inverse
finite Euler transport preserves the radial subspace; combined with scalar
linearity of `R` this gives `R ∘ (N∘J) = N∘J`, i.e. `(I-R)∘(N∘J) = 0`.
Then the band operator `R-Q = (I-Q)-(I-R)` collapses to `(I-Q)`.

This is pure operator algebra on the source-Son carrier. No norm estimate,
Gate 3U bound, sign statement, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSForwardOffSoninReduction

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCausalSupport
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The normalized inverse transport of a source-inclusion image stays inside
the radial subspace: `R ∘ (N∘J) = N∘J`. -/
theorem radialSupportProjection_normalizedInverse_sourceInclusion_eq_self
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L
        (normalizedFiniteEulerInverse family ∘L sourceInclusion lambda) =
      normalizedFiniteEulerInverse family ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  let v : finiteSCarrier := sourceInclusion lambda u
  have hJ : v ∈ ccm24LogRadialSupportClosedSubspace lambda :=
    sourceInclusion_mem_radialSupport lambda u
  have hInv :
      finiteEulerInverseOperator family v ∈
        ccm24LogRadialSupportClosedSubspace lambda := by
    change (ccm24FiniteEulerTransportEquiv family.visiblePrimes).symm v ∈
        ccm24LogRadialSupportClosedSubspace lambda
    exact ccm24FiniteEulerTransportEquiv_symm_mem_logRadialSupport
      lambda family.visiblePrimes hJ
  have hScal :
      (finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerInverseOperator family v ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    (ccm24LogRadialSupportClosedSubspace lambda).smul_mem
      (finiteEulerLowerFactor family.visiblePrimes : ℂ) hInv
  simpa [v, normalizedFiniteEulerInverse, radialSupportProjection,
    Submodule.starProjection_eq_self_iff] using hScal

/-- The forward actual-band coframe is the exact off-Sonin normalized inverse.
   `B∘N∘J = (R-Q)∘(N∘J) = (I-Q)∘(N∘J)` because `(I-R)∘(N∘J) = 0`. -/
theorem sourceActualBandForwardCoframe_eq_offSonin_normalizedInverse
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    sourceActualBandForwardCoframe lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        normalizedFiniteEulerInverse family ∘L sourceInclusion lambda := by
  rw [sourceActualBandForwardCoframe, sourceBandProjection]
  apply ContinuousLinearMap.ext
  intro u
  have hR : radialSupportProjection lambda
        (normalizedFiniteEulerInverse family (sourceInclusion lambda u)) =
      normalizedFiniteEulerInverse family (sourceInclusion lambda u) := by
    exact congrFun (congrArg DFunLike.coe
      (radialSupportProjection_normalizedInverse_sourceInclusion_eq_self
        lambda family)) u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  rw [hR]

end CCM24FiniteSForwardOffSoninReduction
end CCM25Concrete
end Source
end ConnesWeilRH