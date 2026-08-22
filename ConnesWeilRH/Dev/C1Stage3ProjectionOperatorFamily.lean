/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1Stage3ProjectionWindow

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
open scoped InnerProduct InnerProductSpace Topology
open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open C1PositiveTraceLimitBridge
open C1Stage3ProjectionWindow

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
