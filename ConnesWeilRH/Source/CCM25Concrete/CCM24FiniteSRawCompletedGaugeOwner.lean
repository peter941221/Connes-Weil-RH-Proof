/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandCompletedNumerator
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedResponse

/-!
# Lower-factor gauge owner for the raw completed response

The normalized endpoint estimate cannot be divided by the finite Euler lower
factor uniformly.  The completed relative numerator has a different, exact
scalar-gauge symmetry: the numerator and inverse Gram covariance are rescaled
together, so their product remains the raw nonlinear remainder.

This module specializes that paired gauge to the positive finite Euler lower
factor and identifies it with both the actual source remainder and the
canonical completed response.  No norm estimate, Gate 3U bound, or sign claim
is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRawCompletedGaugeOwner

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandCompletedNumerator
open CCM24FiniteSCanonicalCompletedResponse
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The positive finite Euler lower factor, read as a nonzero complex gauge. -/
theorem finiteEulerLowerFactorGauge_ne_zero
    (family : FinitePrimePowerFamily) :
    (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr
    (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))

/-- The completed numerator in the finite Euler lower-factor gauge. -/
noncomputable def lowerFactorGaugedActualBandCompletedRelativeNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  gaugedActualBandCompletedRelativeNumerator owner
    (finiteEulerLowerFactor family.visiblePrimes : ℂ) lambda family

/-- The completed response with the same gauge inserted in its numerator and
inverse Gram covariance. -/
noncomputable def lowerFactorGaugedActualBandCompletedRelativeResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  gaugedActualBandCompletedRelativeResponse owner
    (finiteEulerLowerFactor family.visiblePrimes : ℂ) lambda family

/-- Both pieces of the completed numerator acquire the same paired scalar. -/
theorem lowerFactorGaugedActualBandCompletedRelativeNumerator_eq_scalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeNumerator owner lambda family =
      (star (finiteEulerLowerFactor family.visiblePrimes : ℂ) *
          (finiteEulerLowerFactor family.visiblePrimes : ℂ)) •
        actualBandCompletedRelativeNumerator owner lambda family := by
  exact gaugedActualBandCompletedRelativeNumerator_eq_scalar owner
    (finiteEulerLowerFactor family.visiblePrimes : ℂ) lambda family

/-- The lower-factor gauge reads back as the exact quadratic cycle.  The
inverse lower-factor square is not placed outside this owner. -/
theorem lowerFactorGaugedActualBandCompletedRelativeResponse_eq_quadraticCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      actualBandQuadraticCycledResponse owner lambda family := by
  exact gaugedActualBandCompletedRelativeResponse_eq_quadraticCycle owner
    (finiteEulerLowerFactor family.visiblePrimes : ℂ)
    (finiteEulerLowerFactorGauge_ne_zero family) lambda family

/-- The raw actual remainder is the lower-factor-gauged completed response on
the same source Sonin carrier. -/
theorem lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  rw [lowerFactorGaugedActualBandCompletedRelativeResponse_eq_quadraticCycle,
    ← sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle]

/-- Gauging the complete numerator and its matching inverse covariance changes
neither the un-gauged completed response nor its operator order. -/
theorem lowerFactorGaugedActualBandCompletedRelativeResponse_eq_completed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      actualBandCompletedRelativeResponse owner lambda family := by
  rw [lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder,
    sourceActualBandFiniteEulerRemainderResponse_eq_completedRelativeResponse]

/-- Fixed-family trace legality transfers to the paired gauge owner by the
exact same-object identity, not by scalar division. -/
theorem lowerFactorGaugedActualBandCompletedRelativeResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family) := by
  rw [lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder]
  exact sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor

/-- The lower-factor-gauged owner on the exact family selected by the compact
Weil square. -/
noncomputable def canonicalLowerFactorGaugedCompletedResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : SourceOp lambda :=
  lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda
    (canonicalFamily owner)

/-- The canonical raw remainder is already the paired gauge owner; no external
inverse lower-factor multiplier occurs in this identity. -/
theorem canonicalLowerFactorGaugedCompletedResponse_eq_canonicalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    canonicalLowerFactorGaugedCompletedResponse owner lambda =
      canonicalActualBandCompletedRelativeResponse owner lambda := by
  exact lowerFactorGaugedActualBandCompletedRelativeResponse_eq_completed
    owner lambda (canonicalFamily owner)

end CCM24FiniteSRawCompletedGaugeOwner
end CCM25Concrete
end Source
end ConnesWeilRH
