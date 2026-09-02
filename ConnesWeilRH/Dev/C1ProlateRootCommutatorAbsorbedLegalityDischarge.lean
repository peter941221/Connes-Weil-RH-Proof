/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale
import ConnesWeilRH.Dev.C1ProlateRootCommutatorPerTermNuclearityGlue

/-!
# C1: the S2 absorbed-legality discharge (record 1098)

Records 1097 and 1097b adjudicated the record-1096 primitive fork
numerically: the A-in-HS discharge route is CLOSED for continuum scheduling
(raw trace `Tr K_S` keeps its power law at the certified fine octave, while
the law-16 weighted legs stay O(1)).  The canonical S2 primitive set is now

* (a) `targetProlateDetectorAbsorbedFactorHS`: the detector-ABSORBED factor
  is Hilbert-Schmidt, `Summable i, norm (A (C e_i))^2`.  Its numerical
  witness is the committed record-1068 positive sandwich `p_hs`
  3.5661 -> 3.5356 over four octaves, O(1) and decreasing;
* (b) `targetProlateDetectorRootCommutatorTraceLegality`: trace legality of
  the commutator remainder `C-dagger . [C, K_S]` itself (the leaf's own S2
  obligation).  Its numerical witness is the committed record-1068 nuclear
  norm `l_tr1` 1.3462 -> 1.2850, O(1) and decreasing, with the bounded
  `C-dagger` dressing costing only a fixed constant on the model.

This record wires the record-1095 consumer contract
`targetProlateDetectorRootCommutatorSandwichedTermNuclearity` from (a) and
(b) through the leaf's own law-16 decomposition

```text
  D . K_S  =  C-dagger . K_S . C  +  C-dagger . [C, K_S],
```

that is, `LeftSummand = RightSummand + Remainder`.  The right summand's
diagonal along the global basis is EXACTLY the (a) series, so (a) alone
carries it; the left summand is then the sum of two trace-legal operators.
Record 1096's A-in-HS discharge remains a valid implication but is no
longer the scheduled primitive (map 004 section 4).

RH unclaimed; GATE 1 mainline untouched.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorAbsorbedLegalityDischarge

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale
open C1ProlateRootCommutatorPerTermNuclearityGlue

/-- PRIMITIVE (a): the detector-absorbed prolate factor is Hilbert-Schmidt
along the global basis, `Summable i, norm (A (C e_i))^2`.  This is the
positive sandwich `p_hs = Tr (C-dagger . K_S . C)` of record 1068, measured
O(1) and decreasing over four octaves. -/
noncomputable def targetProlateDetectorAbsorbedFactorHS
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Prop :=
  Summable fun i =>
    ‖targetProlateRemainderFactor unitSoninScale family
        ((CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
          (globalBasis i))‖ ^ 2

/-- Pair data for the absorbed legs: both Hilbert-Schmidt legs are
`A . C` with the common source basis `globalBasis`. -/
noncomputable def targetProlateDetectorAbsorbedPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hAC : targetProlateDetectorAbsorbedFactorHS globalBasis owner family) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateRemainderFactor unitSoninScale family ∘L
    CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  right := targetProlateRemainderFactor unitSoninScale family ∘L
    CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  left_summable_normSq := hAC
  right_summable_normSq := hAC

/-- The absorbed trace product is exactly the second WITH-C-dagger summand:
`(A . C)-dagger . (A . C) = C-dagger . (K_S . C)`. -/
theorem targetProlateDetectorAbsorbedPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hAC : targetProlateDetectorAbsorbedFactorHS globalBasis owner family) :
    (targetProlateDetectorAbsorbedPairData globalBasis owner family hAC).traceProduct =
      targetProlateDetectorRootCommutatorRightSummand owner family := by
  unfold targetProlateDetectorAbsorbedPairData
    BasisHilbertSchmidtPairData.traceProduct
    targetProlateDetectorRootCommutatorRightSummand
  simp only [ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.adjoint_comp]
  rw [← ContinuousLinearMap.comp_assoc
    (targetProlateRemainderFactor unitSoninScale family).adjoint
    (targetProlateRemainderFactor unitSoninScale family)
    (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner),
    targetProlateRemainderFactor_adjoint_comp_self]

/-- The second WITH-C-dagger summand is trace-legal from primitive (a) alone:
its diagonal along the global basis IS the absorbed-factor series. -/
theorem targetProlateDetectorRootCommutatorRightSummand_isTraceClassAlong_of_absorbedHS
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hAC : targetProlateDetectorAbsorbedFactorHS globalBasis owner family) :
    IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorRightSummand owner family) := by
  rw [← targetProlateDetectorAbsorbedPairData_traceProduct_eq
    globalBasis owner family hAC]
  exact (targetProlateDetectorAbsorbedPairData
    globalBasis owner family hAC).traceProduct_isTraceClassAlong

/-- The leaf's own law-16 decomposition as an operator identity:
`LeftSummand = RightSummand + Remainder`, that is,
`C-dagger . C . K_S = C-dagger . K_S . C + C-dagger . [C, K_S]`. -/
theorem targetProlateDetectorRootCommutatorLeftSummand_eq_add
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    targetProlateDetectorRootCommutatorLeftSummand owner family =
      targetProlateDetectorRootCommutatorRightSummand owner family +
        targetProlateDetectorRootCommutatorRemainder owner family := by
  rw [targetProlateDetectorRootCommutatorRemainder_eq_twoSummandDiff]
  abel

/-- The first WITH-C-dagger summand is trace-legal from (a) and (b): it is
the sum of the absorbed right summand and the commutator remainder. -/
theorem targetProlateDetectorRootCommutatorLeftSummand_isTraceClassAlong_of_absorbedHS
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hAC : targetProlateDetectorAbsorbedFactorHS globalBasis owner family)
    (hrem : targetProlateDetectorRootCommutatorTraceLegality
      owner family globalBasis) :
    IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorLeftSummand owner family) := by
  unfold targetProlateDetectorRootCommutatorTraceLegality at hrem
  rw [targetProlateDetectorRootCommutatorLeftSummand_eq_add owner family]
  exact isTraceClassAlong_add globalBasis _ _
    (targetProlateDetectorRootCommutatorRightSummand_isTraceClassAlong_of_absorbedHS
      globalBasis owner family hAC)
    hrem

/-- DISCHARGE: the record-1095 consumer contract follows from the canonical
primitive set (a) absorbed-factor HS and (b) commutator-remainder trace
legality, through the leaf's own law-16 decomposition.  The raw-root
A-in-HS primitive of record 1096 is not used. -/
theorem targetProlateDetectorRootCommutatorSandwichedTermNuclearity_of_absorbedLegality
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hAC : targetProlateDetectorAbsorbedFactorHS globalBasis owner family)
    (hrem : targetProlateDetectorRootCommutatorTraceLegality
      owner family globalBasis) :
    targetProlateDetectorRootCommutatorSandwichedTermNuclearity
      globalBasis owner family := by
  constructor
  · exact targetProlateDetectorRootCommutatorLeftSummand_isTraceClassAlong_of_absorbedHS
      globalBasis owner family hAC hrem
  · exact targetProlateDetectorRootCommutatorRightSummand_isTraceClassAlong_of_absorbedHS
      globalBasis owner family hAC

end C1ProlateRootCommutatorAbsorbedLegalityDischarge
end Source
end ConnesWeilRH
