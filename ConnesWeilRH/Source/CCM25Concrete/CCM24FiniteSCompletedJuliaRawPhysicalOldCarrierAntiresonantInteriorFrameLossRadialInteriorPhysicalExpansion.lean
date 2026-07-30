/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedMovingCrossing

/-!
# Radial interior physical expansion

Proof 675 gives the exact signed physical owner for the compressed radial
channel.  At the endpoint `alpha = 1`, the actual suffix Sonin projection is
the canonical moving projection, and the latter has the literal decomposition

```text
P_S = E Q_S E - K_S.
```

The compressed translation/Sonin commutator is therefore the negative of the
CC20 three-branch commutator.  All branches stay signed; this module makes no
norm, positivity, or cancellation claim.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialInteriorPhysicalExpansion

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossCommutator
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open CCM24FiniteSCompletedMovingCrossing
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Endpoint projection identity -/

/-- The actual suffix Sonin projection is the endpoint compression-minus-prolate
decomposition on the common radial carrier. -/
theorem newSuffixRangeProjection_eq_radialCompression_sub_prolate
    (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection unitSoninScale S =
      compressedSecondSupport
          (radialSupportProjection unitSoninScale)
          (parameterizedFourierSupportProjection unitSoninScale 1 S
            (by norm_num)) -
        parameterizedProlateRemainder unitSoninScale 1 S (by norm_num) := by
  rw [newSuffixRangeProjection_eq_parameterizedCanonicalGramProjection,
    parameterizedCanonicalGramProjection_eq_compression_sub_prolate]

/-! ## Signed three-branch readback -/

/-- Reversing the commutator orientation turns the compressed radial interior
channel into the negative signed three-branch physical owner. -/
theorem radialInteriorSoninCommutator_eq_neg_threeBranch
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialInteriorSoninCommutator p S =
      -cc20ThreeBranchCommutator
        (radialSupportProjection unitSoninScale)
        (parameterizedFourierSupportProjection unitSoninScale 1 S
          (by norm_num))
        (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
        (radialCompressedPositiveTranslation p) := by
  have hprojection :=
    newSuffixRangeProjection_eq_radialCompression_sub_prolate S
  have hthree := cc20Commutator_eq_threeBranch_of_eq
    (radialSupportProjection unitSoninScale)
    (parameterizedFourierSupportProjection unitSoninScale 1 S (by norm_num))
    (newSuffixRangeProjection unitSoninScale S)
    (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
    (radialCompressedPositiveTranslation p)
    hprojection
  have hswap :
      cc20Commutator (radialCompressedPositiveTranslation p)
          (newSuffixRangeProjection unitSoninScale S) =
        -cc20Commutator (newSuffixRangeProjection unitSoninScale S)
          (radialCompressedPositiveTranslation p) := by
    unfold cc20Commutator
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
    abel
  rw [radialInteriorSoninCommutator, hswap, hthree]

end AntiresonantFrameLossRadialInteriorPhysicalExpansion
end CCM25Concrete
end Source
end ConnesWeilRH
