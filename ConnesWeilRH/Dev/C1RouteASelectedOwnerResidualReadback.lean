/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1HealthyYoshidaCorrectionFamily
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1P2BilateralProfile

/-!
# Route A, round 1: selected-owner finite-profile readback

This leaf binds the exact finite-prime readback to the parameterized selected
owner used by the healthy detector construction.  It does not estimate the
sign.  It removes the opaque `finitePrimeSum` presentation from the first
round's producer obligation and leaves the actual finite visible profile as
the sole arithmetic input.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteASelectedOwnerResidualReadback

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaCorrectionFamily
open C1HealthyYoshidaDetector
open C1LocalConfigurationDomination
open C1P2BilateralProfile
open C1P2PrimePointMatching
open C1SameOwnerWeil

noncomputable section

theorem selectedOwner_gate_eq_archimedean_plus_visibleProfile
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) :
    ICgate (selectedOwner base (family.value y) n).convolutionSquare =
      archimedeanTerm
          (selectedOwner base (family.value y) n).convolutionSquare +
        selectedOwnerVisiblePrimeProfileWeightedSum family base n y := by
  let owner := selectedOwner base (family.value y) n
  have hsquare : owner.sourceTest.convolutionSquare = owner.convolutionSquare := by
    simp [owner, selectedOwner_sourceTest, selectedOwner_convolutionSquare]
  rw [← hsquare, ← p2AggregateValue_eq_ICgate_convolutionSquare owner.sourceTest]
  rw [p2AggregateValue_eq_archimedean_plus_finiteProfile]
  rw [← finitePrimeSum_eq_bilateralProfile_weighted_sum, hsquare]
  exact congrArg (fun z => archimedeanTerm owner.convolutionSquare + z)
    (selectedOwnerFinitePrimeSum_eq_visibleProfileWeightedSum family base n y)

theorem selectedOwner_gate_nonpos_iff_visibleProfile_budget
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) :
    ICgate (selectedOwner base (family.value y) n).convolutionSquare ≤ 0 ↔
      archimedeanTerm
          (selectedOwner base (family.value y) n).convolutionSquare +
        selectedOwnerVisiblePrimeProfileWeightedSum family base n y ≤ 0 := by
  rw [selectedOwner_gate_eq_archimedean_plus_visibleProfile]

theorem selectedOwner_qw_eq_neg_archimedean_sub_visibleProfile
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex)
    (hvanishes :
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet
        (selectedOwner base (family.value y) n).sourceTest) :
    qw (selectedOwner base (family.value y) n).sourceTest =
      -archimedeanTerm
          (selectedOwner base (family.value y) n).convolutionSquare -
        selectedOwnerVisiblePrimeProfileWeightedSum family base n y := by
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    _ hvanishes]
  have hsquare :
      (selectedOwner base (family.value y) n).sourceTest.convolutionSquare =
        (selectedOwner base (family.value y) n).convolutionSquare := by
    simp [selectedOwner_sourceTest, selectedOwner_convolutionSquare]
  rw [hsquare, selectedOwnerFinitePrimeSum_eq_visibleProfileWeightedSum]

end
end C1RouteASelectedOwnerResidualReadback
end Source
end ConnesWeilRH
