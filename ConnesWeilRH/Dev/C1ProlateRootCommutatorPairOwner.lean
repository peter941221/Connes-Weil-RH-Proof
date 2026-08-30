/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale

/-!
# C1: root-commutator pair owner for S2 at unit scale (record 1065)

This leaf builds a named-basis trace-legality owner for the active-order root
commutator `cc20Commutator(C, K_S)` = `C oL K_S - K_S oL C`, where `C` is the
selected convolution root and `K_S` is the finite-S prolate remainder.  The
base pair data owns `K_S` as the positive square of its bounded factor

```text
F_K := targetProlateRemainderFactor unitSoninScale family = Q_S (E - R_S) .
```

Two bounded-sandwich transports place the root on either side of that square;
an `l2Sum` with scalar `-1` forms the signed difference.  The only analytic
obligation introduced here is named-basis Hilbert--Schmidt summability of
`F_K` itself, `targetProlateRemainderFactorSummable`.  The root never appears
as a Hilbert--Schmidt leg: it enters only as a bounded sandwich dressing, so
no self-adjointness or unitarity assumption on the root is required.

This mirrors the source-side sibling owner in
`CCM25Concrete.CCM24FiniteSProlateCommutatorTraceBound`, which owns the same
signed-difference shape for the detector commutator; here the target remainder
factor replaces the source prolate factor and the convolution root replaces the
detector operator.  The leaf is a LEGALITY owner: it proves summability of the
named-basis diagonal series via Cauchy--Schwarz on Hilbert--Schmidt legs, not
size estimates.  The semilocal four-branch chain (record 1064) remains the
estimate route feeding ledger branch decay.

No positivity, remainder sign, or RH-facing statement is asserted here; no F1'
closure is claimed until both S1 and `targetProlateRemainderFactorSummable`
are discharged by producers.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorPairOwner

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable section

/-- Named-basis Hilbert--Schmidt summability of the bounded prolate-remainder
factor `Q_S (E - R_S)` itself, without root dressing.  This is the single new
S2 analytic obligation from record 1065; unlike the S1 contract it does not
depend on the selected owner. -/
noncomputable def targetProlateRemainderFactorSummable
    (family : FinitePrimePowerFamily) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  Summable fun i =>
    ‖targetProlateRemainderFactor unitSoninScale family (globalBasis i)‖ ^ 2

/-- Base pair owner for the finite-S remainder as the positive square of its
bounded factor. -/
noncomputable def targetProlateRemainderSquarePairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateRemainderFactor unitSoninScale family
  right := targetProlateRemainderFactor unitSoninScale family
  left_summable_normSq := hfactor
  right_summable_normSq := hfactor

/-- The base trace product is the finite-S remainder itself. -/
theorem targetProlateRemainderSquarePairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRemainderSquarePairData globalBasis family hfactor).traceProduct =
      targetProlateRemainder unitSoninScale family := by
  unfold targetProlateRemainderSquarePairData BasisHilbertSchmidtPairData.traceProduct
  exact targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family

/-- Left-side transport: the selected convolution root on the left of the
remainder square. -/
noncomputable def targetProlateRootLeftRemainderPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis :=
  targetProlateRemainderSquarePairData globalBasis family hfactor
    |>.boundedSandwich globalBasis
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
      (ContinuousLinearMap.id ℂ finiteSCarrier)

/-- The left-side trace product is the root applied on the left of the
remainder. -/
theorem targetProlateRootLeftRemainderPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRootLeftRemainderPairData globalBasis owner family hfactor).traceProduct =
      CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner ∘L
        targetProlateRemainder unitSoninScale family := by
  unfold targetProlateRootLeftRemainderPairData
  rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    targetProlateRemainderSquarePairData_traceProduct_eq]
  simp only [ContinuousLinearMap.comp_id]

/-- Right-side transport: the selected convolution root on the right of the
remainder square. -/
noncomputable def targetProlateRemainderRightRootPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis :=
  targetProlateRemainderSquarePairData globalBasis family hfactor
    |>.boundedSandwich globalBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier)
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)

/-- The right-side trace product is the root applied on the right of the
remainder. -/
theorem targetProlateRemainderRightRootPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRemainderRightRootPairData globalBasis owner family hfactor).traceProduct =
      targetProlateRemainder unitSoninScale family ∘L
        CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner := by
  unfold targetProlateRemainderRightRootPairData
  rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    targetProlateRemainderSquarePairData_traceProduct_eq]
  simp only [ContinuousLinearMap.id_comp]

/-- The signed-difference owner for the complete root commutator: the two
one-sided transports combined over the `L2` product carrier, with the minus
sign kept in the second right leg. -/
noncomputable def targetProlateRootCommutatorPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (finiteSCarrier × finiteSCarrier)) globalBasis :=
  BasisHilbertSchmidtPairData.l2Sum
    (targetProlateRootLeftRemainderPairData globalBasis owner family hfactor)
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight
      (targetProlateRemainderRightRootPairData globalBasis owner family hfactor) (-1))

/-- The signed-difference trace product is exactly the root commutator. -/
theorem targetProlateRootCommutatorPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRootCommutatorPairData globalBasis owner family hfactor).traceProduct =
      cc20Commutator (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
        (targetProlateRemainder unitSoninScale family) := by
  unfold targetProlateRootCommutatorPairData
  rw [BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    targetProlateRootLeftRemainderPairData_traceProduct_eq,
    targetProlateRemainderRightRootPairData_traceProduct_eq]
  simp only [sub_eq_add_neg, neg_one_smul, cc20Commutator]

/-- S2 closes from the single prolate-factor Hilbert--Schmidt contract.  The
`factorBasis` over the `L2` product carrier is an existence-side argument: it
is required by the trace-legality machinery but carries no analytic content of
its own. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_remainderFactorSummable
    {ν κ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (factorBasis : HilbertBasis κ ℂ (WithLp 2 (finiteSCarrier × finiteSCarrier)))
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  exact targetProlateDetectorRootCommutatorTraceLegality_of_pairData
      globalBasis factorBasis owner family
      (targetProlateRootCommutatorPairData globalBasis owner family hfactor)
      (targetProlateRootCommutatorPairData_traceProduct_eq
        globalBasis owner family hfactor)

/-- F1' at unit scale follows from the S1 smoothing contract and the single
prolate-factor Hilbert--Schmidt contract. -/
theorem targetProlateRemainderDetectorWeightedTraceLegality_of_rightSmoothing_and_remainderFactorSummable
    {ν κ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (factorBasis : HilbertBasis κ ℂ (WithLp 2 (finiteSCarrier × finiteSCarrier)))
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hright : targetProlateDetectorRightSmoothingFactorSummable owner family globalBasis)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    targetProlateRemainderDetectorWeightedTraceLegality owner family globalBasis := by
  have hcomm := targetProlateDetectorRootCommutatorTraceLegality_of_remainderFactorSummable
      globalBasis factorBasis owner family hfactor
  exact targetProlateRemainderDetectorWeightedTraceLegality_of_rightSmoothing_and_rootCommutator
      globalBasis owner family hright hcomm

end

end C1ProlateRootCommutatorPairOwner
end Source
end ConnesWeilRH
