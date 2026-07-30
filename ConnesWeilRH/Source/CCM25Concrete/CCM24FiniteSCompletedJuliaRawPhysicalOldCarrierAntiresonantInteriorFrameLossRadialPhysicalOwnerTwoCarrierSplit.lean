/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerComplement

/-!
# Two-carrier split of the signed radial physical owner

Proof 679 combines the upper and complementary radial readouts into one
canonical same-domain normal form.  The owner is first decomposed by the
actual complementary projections, then those two channels are replaced by
their signed source objects.

No estimate or positivity statement is made.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerTwoCarrierSplit

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialInteriorPhysicalExpansion
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerCompression
open AntiresonantFrameLossRadialPhysicalOwnerComplement
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Projection decomposition -/

/-- Every signed radial owner is the sum of its upper and complementary
radial compressions. -/
theorem radialSignedPhysicalOwner_eq_twoCarrierCompression
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSignedPhysicalOwner p S =
      radialSupportProjection unitSoninScale ∘L
          radialSignedPhysicalOwner p S +
        radialComplement unitSoninScale ∘L
          radialSignedPhysicalOwner p S := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  abel

/-! ## Canonical signed two-channel normal form -/

/-- The two carrier compressions read back as the upper signed three-branch
channel plus the lower radial boundary channel. -/
theorem radialSignedPhysicalOwner_eq_upperThreeBranch_add_boundary
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSignedPhysicalOwner p S =
      radialSupportProjection unitSoninScale ∘L
          (-cc20ThreeBranchCommutator
            (radialSupportProjection unitSoninScale)
            (parameterizedFourierSupportProjection unitSoninScale 1 S
              (by norm_num))
            (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
            (radialCompressedPositiveTranslation p)) +
        radialSoninBoundaryCrossing p S := by
  rw [radialSignedPhysicalOwner_eq_twoCarrierCompression,
    radialSupportProjection_comp_radialSignedPhysicalOwner_eq_neg_threeBranch,
    radialComplement_comp_radialSignedPhysicalOwner_eq_boundary]

end AntiresonantFrameLossRadialPhysicalOwnerTwoCarrierSplit
end CCM25Concrete
end Source
end ConnesWeilRH
