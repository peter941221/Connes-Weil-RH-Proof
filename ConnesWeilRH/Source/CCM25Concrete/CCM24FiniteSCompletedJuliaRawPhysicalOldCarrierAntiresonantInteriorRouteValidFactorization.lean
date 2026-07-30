/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization

/-!
# Route-valid quantifiers for the antiresonant physical factor

The finite-prime route never inserts the same visible prime twice.  Its
canonical list is deduplicated, and every adjacent step occurs on a suffix
`p :: S` of that list.  Consequently the actual step domain is

```text
(p :: S).Nodup,
```

not the larger domain of all prime/list pairs used by the earlier uniform
producer contract.  This module records the weaker route-valid contract,
proves its exact equivalence in physical-factor and joint-gap coordinates,
and specializes it to every suffix of an actual finite prime-power family.

No route-valid factor is constructed here.  The result removes an unnecessary
repeated-prime obligation; it does not close Bone 1 or Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization

open CC20Concrete
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout
open CCM24FiniteSProjectionTrace

/-! ## The actual adjacent-step domain -/

/-- A prime/suffix pair is route-valid when adjoining the current prime keeps
the visible-prime list deduplicated. -/
def SuffixRouteValidStep (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : Prop :=
  (p :: S).Nodup

theorem suffixRouteValidStep_iff
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    SuffixRouteValidStep p S ↔ p ∉ S ∧ S.Nodup := by
  exact List.nodup_cons

/-- Every suffix step of an actual finite prime-power family is route-valid.
The proof uses the deduplication theorem owned by that family, not an added
arithmetic premise. -/
theorem suffixRouteValidStep_of_isSuffix_visiblePrimes
    (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hsuffix : p :: S <:+ family.visiblePrimes) :
    SuffixRouteValidStep p S := by
  exact hsuffix.nodup family.visiblePrimes_nodup

/-! ## Route-valid producer contracts -/

/-- One common physical-factor bound on every deduplicated adjacent step. -/
structure SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRouteValidStep p S →
      SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
        owner lambda p S bound

/-- The same route-valid producer in synchronized joint-gap coordinates. -/
structure SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRouteValidStep p S →
      SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S bound

/-! ## Exact coordinate equivalence on the restricted domain -/

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData.toRouteJointGapReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
        owner lambda bound) :
    SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S hvalid =>
      ((data.factor p S hvalid).toResponseReadoutData).toJointGapReadoutData }

noncomputable def
    SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData.toRoutePhysicalFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData
      owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S hvalid =>
      _root_.ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization.SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toInteriorPhysicalFactorData
        (_root_.ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout.SuffixRawOldCarrierCoframeJointGapReadoutData.toResponseReadoutData
          (data.readout p S hvalid)) }

theorem exists_routeUniformPhysicalFactor_iff_exists_routeUniformJointGapReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
          owner lambda bound) ↔
      Nonempty
        (SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData
          owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toRouteJointGapReadoutData⟩
  · rintro ⟨data⟩
    exact ⟨data.toRoutePhysicalFactorData⟩

/-! ## Comparison with the earlier over-quantified contracts -/

/-- The all-list physical contract implies the route-valid one without a norm
cost.  The converse is deliberately not asserted. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData.toRouteUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
      owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S _ => data.factor p S }

/-- The all-list joint-gap contract likewise restricts to the route-valid
domain with the same bound. -/
noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toRouteUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapReadoutData
      owner lambda bound) :
    SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S _ => data.readout p S }

/-! ## Actual finite-family specialization -/

/-- Select the physical factor for any genuine suffix of an actual finite
prime-power family. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData.forFamilySuffix
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
        owner lambda bound)
    (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hsuffix : p :: S <:+ family.visiblePrimes) :
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound :=
  data.factor p S
    (suffixRouteValidStep_of_isSuffix_visiblePrimes family p S hsuffix)

/-- Select the equivalent joint-gap readout on the same genuine suffix. -/
noncomputable def
    SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData.forFamilySuffix
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeRouteUniformJointGapReadoutData
      owner lambda bound)
    (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hsuffix : p :: S <:+ family.visiblePrimes) :
    SuffixRawOldCarrierCoframeJointGapReadoutData
      owner lambda p S bound :=
  data.readout p S
    (suffixRouteValidStep_of_isSuffix_visiblePrimes family p S hsuffix)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
