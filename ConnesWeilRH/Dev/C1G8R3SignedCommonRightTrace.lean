/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3CommonRightCausalTelescope
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRenewalRootPairing

/-!
# R3 signed paired owner for the common-right telescope

The finite visible-prime coboundary telescope is a right-leg identity.  The
source trace theory owns the corresponding complete corner, however, rather
than the common-right leg in isolation.  This leaf pairs the two interfaces
before any Schatten claim is made and transfers the existing physical
trace-class theorem to the explicitly telescoped operator.

No Hilbert--Schmidt assertion for the common-right leg is made here.  The
consumer is the signed, detector-specific same-owner trace route toward the
healthy CompactLog B5 statement.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSInverseMetric
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSCausalMarkov
open Source.CCM25Concrete.CCM24FiniteSCausalMarkovFirstDifference
open Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRenewalRootPairing

/- The exact paired form of the 1455 common-right telescope. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_coboundaryPaired
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
        (rootConvolution owner ∘L sourceSoninProjection lambda ∘L
          normalizedFiniteEulerInverseList_coboundaryTelescope
            family.visiblePrimes ∘L sourceBandProjection lambda) := by
  rw [sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair,
    sourceRootCompletedFiniteEulerCommonRightLeg_eq_coboundaryTelescope]

/- The physical three-branch owner supplies trace legality for the explicitly
telescoped paired operator.  In particular, this theorem does not ask for an
individual common-right Hilbert--Schmidt estimate. -/
theorem sourceRootCompletedFiniteEulerCorner_coboundaryPaired_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
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
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong globalBasis
      ((rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
        (rootConvolution owner ∘L sourceSoninProjection lambda ∘L
          normalizedFiniteEulerInverseList_coboundaryTelescope
            family.visiblePrimes ∘L sourceBandProjection lambda)) := by
  rw [← sourceRootCompletedFiniteEulerCorner_eq_coboundaryPaired]
  exact sourceRootCompletedFiniteEulerCorner_isTraceClassAlong owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor

end Dev
end ConnesWeilRH
