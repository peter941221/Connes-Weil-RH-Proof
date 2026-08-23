/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1Stage3ProjectionWindow
import ConnesWeilRH.Dev.C1Stage3ProjectionResponseBridge

/-!
# C1 Stage-3 projection cutoff operator family

The finite-window projection owner is a positive operator

```text
  C_n† K_S C_n
```

whose trace-class proof comes from the Hilbert--Schmidt pair ledger.  It is
not definitionally a same-factor `F†F`, so it uses the operator-level
`PositiveTraceOperatorLimitFamily` contract.  This file supplies the concrete
cutoff sequence and keeps the only unresolved analytic inputs explicit:
the real remainder must tend to zero and the corrected trace must read back to
the same-owner `qw` value.

No cutoff limit, remainder estimate, arithmetic readback, or RH conclusion is
asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1Stage3ProjectionOperatorFamily

open Filter
open MeasureTheory
open scoped InnerProduct InnerProductSpace Topology
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.SelectedWeilSquare
open C1CrossingCommonCarrier
open C1CrossingEulerLogReadback
open C1PositiveTraceCutoffAdapter
open C1PositiveTraceLimitBridge
open C1Stage3CarrierReadback
open C1Stage3ProjectionWindow
open C1Stage3ProjectionResponseBridge
open C1Stage3ProjectionTraceLedger

noncomputable section

abbrev projectionCarrier := cc20GlobalLogCrossingL2

/-! The operator carried by the `n`th fixed-carrier cutoff. -/

noncomputable def cutoffProjectionOperator
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    projectionCarrier →L[ℂ] projectionCarrier :=
  (cutoffProjectionPairData g lambda S globalBasis n).traceProduct

theorem cutoffProjectionOperator_eq_traceProduct
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    cutoffProjectionOperator g lambda S globalBasis n =
      (cutoffProjectionPairData g lambda S globalBasis n).traceProduct := rfl

theorem cutoffProjectionOperator_isTraceClassAlong
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    IsTraceClassAlong globalBasis
      (cutoffProjectionOperator g lambda S globalBasis n) := by
  exact cutoffProjectionPairData_traceProduct_isTraceClassAlong
    g lambda S globalBasis n

theorem cutoffProjectionOperator_isPositive
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    (cutoffProjectionOperator g lambda S globalBasis n).IsPositive := by
  exact cutoffProjectionPairData_traceProduct_isPositive
    g lambda S globalBasis n

theorem cutoffProjectionOperator_trace_re_nonnegative
    {nu : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis nu ℂ projectionCarrier) (n : Nat) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (cutoffProjectionOperator g lambda S globalBasis n)).re := by
  exact positiveTraceOperator_re_nonnegative globalBasis
    (cutoffProjectionOperator g lambda S globalBasis n)
    (cutoffProjectionOperator_isPositive g lambda S globalBasis n)
    (cutoffProjectionOperator_isTraceClassAlong g lambda S globalBasis n)

/-! The concrete cutoff owner now has an exact response ledger.  The two
defects remain visible: this theorem is an identity, not a remainder estimate.
-/

theorem ordinaryTraceAlong_cutoffProjectionOperator_eq_projectionResponse_add_defects
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) (n : Nat) :
    ordinaryTraceAlong globalBasis
        (cutoffProjectionOperator owner.sourceTest lambda S globalBasis n) =
      ordinaryTraceAlong globalBasis (projectionResponse owner lambda S) +
        ordinaryTraceAlong globalBasis
          (kernelInsertionSandwich owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
            lambda S) +
        ordinaryTraceAlong globalBasis
          (windowToResponseDefect owner
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
            lambda S) := by
  simpa only [cutoffProjectionOperator, cutoffProjectionPairData] using
    (ordinaryTraceAlong_fullBoundaryProjectionPairData_eq_projectionResponse_add_defects
      owner (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
      lambda S (cutoffFullBasis owner.sourceTest n)
      (cutoffOutputBasis owner.sourceTest n) globalBasis hresponse)

/-! Attach the same cutoff owner to the active finite arithmetic scalar.  The
common-carrier certificate and the selected response trace class stay explicit;
the residual and both window defects are not hidden in a definition.
-/

theorem realTrace_cutoffProjectionOperator_eq_selectedArithmetic_add_defects
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (n : Nat)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous (cutoffLower owner.sourceTest n)
        (cutoffUpper owner.sourceTest n) (canonicalCrossingLengthSet owner))
    (hsupp : Function.support owner.sourceTest.test ⊆
      Set.Icc (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure
        (BoundaryFullInputInterval (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n)))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure
        (BoundaryOutputInterval (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n)))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (basisData : ∀ pm : {pm // pm ∈ canonicalPrimePowerTerms owner},
      GlobalPrimePowerTraceBasisData (cutoffLower owner.sourceTest n)
        (cutoffUpper owner.sourceTest n) pm.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    (ordinaryTraceAlong globalBasis
      (cutoffProjectionOperator owner.sourceTest lambda S globalBasis n)).re =
      selectedArithmeticCarrierSum owner +
        (ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda S
            (canonicalPrimePowerTerms owner))).re +
        (ordinaryTraceAlong globalBasis
          (kernelInsertionSandwich owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
            lambda S)).re +
        (ordinaryTraceAlong globalBasis
          (windowToResponseDefect owner
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
            lambda S)).re := by
  simpa only [cutoffProjectionOperator, cutoffProjectionPairData] using
    (realTrace_fullBoundaryProjectionPairData_eq_selectedArithmetic_add_defects
      owner (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
      lambda S data hsupp fullBasis outputBasis globalBasis basisData hresponse)

/-! The two missing analytic fields are data, not definitions. -/

structure ProjectionCutoffLimitContracts
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) where
  remainder : Nat → Real
  remainder_tendsto_zero :
    Tendsto remainder atTop (𝓝 (0 : Real))
  readback_tendsto_qw :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffProjectionOperator g lambda S globalBasis n)).re -
            remainder n)
      atTop (𝓝 (C1SameOwnerWeil.qw g))

noncomputable def positiveTraceOperatorLimitFamilyOfProjectionCutoffContracts
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (contracts : ProjectionCutoffLimitContracts g lambda S globalBasis) :
    PositiveTraceOperatorLimitFamily globalBasis g where
  traceOperator := cutoffProjectionOperator g lambda S globalBasis
  traceClass := fun n => cutoffProjectionOperator_isTraceClassAlong
    g lambda S globalBasis n
  positive := fun n => cutoffProjectionOperator_isPositive
    g lambda S globalBasis n
  remainder := contracts.remainder
  remainder_tendsto_zero := contracts.remainder_tendsto_zero
  readback_tendsto_qw := contracts.readback_tendsto_qw

theorem qw_nonnegative_of_projectionCutoffLimitContracts
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (contracts : ProjectionCutoffLimitContracts g lambda S globalBasis) :
    0 ≤ C1SameOwnerWeil.qw g :=
  qw_nonnegative_of_positiveTraceOperatorLimitFamily
    (positiveTraceOperatorLimitFamilyOfProjectionCutoffContracts
      g lambda S globalBasis contracts)

theorem healthyCriterionState_of_projectionCutoffLimitContracts
    {ν : Type*} [Countable ν]
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (F : Finset CriticalVanishingPoint)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (hcontracts : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace F g →
        ProjectionCutoffLimitContracts g lambda S globalBasis) :
    C1.healthyCriterionState F := by
  apply healthyCriterionState_of_positiveTraceOperatorLimitFamily
    globalBasis F
  intro g hvanishing
  exact positiveTraceOperatorLimitFamilyOfProjectionCutoffContracts
    g lambda S globalBasis (hcontracts g hvanishing)

end
end C1Stage3ProjectionOperatorFamily
end Dev
end Source
end ConnesWeilRH
