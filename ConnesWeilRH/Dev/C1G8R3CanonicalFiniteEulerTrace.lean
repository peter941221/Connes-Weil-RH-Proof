/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum
import ConnesWeilRH.Dev.C1G8P1CanonicalFamily
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRenewalRootPairing

/-!
# All-scale trace owner for the canonical finite-Euler source corner

The all-scale source prolate square-sum supplies the trace-legality input for
the selected owner's canonical finite-prime family.  The resulting trace is
read back as the existing ordered basis/renewal pairing.  This closes the
finite-Euler source-corner trace interface; it does not identify that corner
with the G8 cutoff trace or its Weil limit.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSCausalMarkov
open Source.CCM25Concrete.CCM24FiniteSInverseMetric
open Source.CCM25Concrete.CCM24FiniteSMultiRenewal
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRootPairing
open Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRenewalRootPairing
open Source.C1G8P1CanonicalFamily
open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

set_option maxHeartbeats 1000000

/-- The source finite-Euler corner for the tower owner's exact canonical
visible-prime family is trace-class at every selected Sonin scale, along the
same named global basis used by the source prolate factor. -/
theorem g8CanonicalSourceFiniteEulerCorner_isTraceClassAlong_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ Carrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c)) :
    IsTraceClassAlong globalBasis
      (sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse (g8CanonicalFamily owner) ∘L
            radialSupportProjection lambda)) := by
  exact sourceRootCompletedFiniteEulerCorner_isTraceClassAlong owner lambda
    (g8CanonicalFamily owner) a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)

/-- The canonical finite-Euler corner has the exact ordered renewal readback
on the same global basis.  The basis sum remains outside the renewal sum. -/
theorem g8CanonicalSourceFiniteEulerCorner_trace_eq_orderedRenewalPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ Carrier) :
    ordinaryTraceAlong globalBasis
        (sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse (g8CanonicalFamily owner) ∘L
              radialSupportProjection lambda)) =
      ∑' index : ν,
        ∑' renewalIndex : FiniteEulerRenewalIndex
            (g8CanonicalFamily owner).visiblePrimes,
          (finiteEulerRenewalWeight
              (g8CanonicalFamily owner).visiblePrimes renewalIndex : ℂ) *
            rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
              (finiteEulerRenewalDisplacement
                (g8CanonicalFamily owner).visiblePrimes renewalIndex)
              globalBasis index := by
  exact sourceRootCompletedFiniteEulerTrace_eq_iterated_rootPairing_tsum
    owner lambda (g8CanonicalFamily owner) globalBasis

end Dev
end ConnesWeilRH
