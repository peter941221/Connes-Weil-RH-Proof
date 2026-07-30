/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialInteriorPhysicalExpansion

/-!
# Signed radial physical owner

Proof 676 recombines the exact radial interior expansion with the radial
boundary channel.  The complete relative translation/Sonin commutator is
represented by one signed owner containing the negative CC20 three-branch
ledger and the positive-translation boundary crossing.

No term is estimated, discarded, or declared positive.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwner

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossCommutator
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialInteriorPhysicalExpansion
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Complete signed owner -/

/-- The complete signed radial physical owner: the negative three-branch
interior ledger plus the one-sided radial boundary crossing. -/
noncomputable def radialSignedPhysicalOwner
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  -cc20ThreeBranchCommutator
      (radialSupportProjection unitSoninScale)
      (parameterizedFourierSupportProjection unitSoninScale 1 S (by norm_num))
      (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
      (radialCompressedPositiveTranslation p) +
    radialSoninBoundaryCrossing p S

/-- The full relative translation/Sonin commutator is exactly the signed
physical owner. -/
theorem suffixPrimeTranslationProjectionCommutator_eq_radialSignedPhysicalOwner
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixPrimeTranslationProjectionCommutator p S =
      radialSignedPhysicalOwner p S := by
  rw [suffixPrimeTranslationProjectionCommutator_eq_radialInterior_add_boundary,
    radialInteriorSoninCommutator_eq_neg_threeBranch]
  rfl

end AntiresonantFrameLossRadialPhysicalOwner
end CCM25Concrete
end Source
end ConnesWeilRH
