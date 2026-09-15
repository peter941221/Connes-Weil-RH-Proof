/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace

/-!
# Moving-scale source Sonin commutator trace legality

The all-scale prolate-factor square-sum supplies the existing complete
three-branch source trace ledger at every selected Sonin scale.  The signed
commutator stays intact; this theorem does not estimate its leakage branch in
isolation or identify the source trace with the G8 cutoff limit.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24ReflectedCompactRoot

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

/-- The complete signed source Sonin-detector commutator is trace-class
along the same named global basis at every selected scale. -/
theorem sourceSoninDetectorCommutator_isTraceClassAlong_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
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
    (globalBasis : HilbertBasis ν ℂ Carrier) :
    IsTraceClassAlong globalBasis
      (cc20Commutator (sourceSoninProjection lambda)
        (detectorOperator owner)) := by
  rw [sourceSoninCommutator_eq_threeBranch]
  exact sourceThreeBranchCommutator_isTraceClassAlong owner lambda a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)

/-- The ordinary trace of the full source Sonin commutator splits into the
already-owned outer pair and the still-coupled second-support/prolate
remainder, at every selected scale and along the same global basis. -/
theorem sourceSoninDetectorCommutator_trace_eq_outerPair_add_remainder_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
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
    (globalBasis : HilbertBasis ν ℂ Carrier) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20Commutator (sourceSoninProjection lambda)
          (detectorOperator owner)) =
      PositiveTrace.ordinaryTraceAlong globalBasis
          (cc20OuterCommutatorBranch (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (detectorOperator owner) +
            cc20ReflectedOuterCommutatorBranch
              (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (detectorOperator owner)) +
        PositiveTrace.ordinaryTraceAlong globalBasis
          (sourceSecondSupportProlateRemainder owner lambda) := by
  have houter := sourceOuterCommutatorPair_isTraceClassAlong owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hremainder := sourceSecondSupportProlateRemainder_isTraceClassAlong
    owner lambda a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)
  rw [sourceSoninCommutator_eq_threeBranch,
    sourceThreeBranchCommutator_eq_outerPair_add_remainder]
  exact PositiveTrace.ordinaryTraceAlong_add globalBasis _ _ houter hremainder

end Dev
end ConnesWeilRH
