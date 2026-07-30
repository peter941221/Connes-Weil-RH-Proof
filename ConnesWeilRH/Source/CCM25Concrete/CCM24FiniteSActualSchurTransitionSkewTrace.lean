/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTransitionOrientation

/-!
# Trace cycle for the transition-skew coboundary

The orientation ledger leaves the signed term

```text
M_S A - A M_(p::S),   A = T - T†,
```

where each boundary moment is the adjoint of a complete raw response.  This
module gives that term one legal Hilbert--Schmidt owner.  It cycles each
source-carrier product to the common target carrier and keeps the difference
signed.  The result is a trace relocation, not a cancellation or a norm
estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurTransitionSkewTrace

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace

variable {ι κ H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

local notation "TraceH" =>
  ordinaryTraceAlong (H := H)
local notation "TraceG" =>
  ordinaryTraceAlong (H := G)

/-! ## One-sided cycles -/

theorem ordinaryTraceAlong_adjointPair_comp_skew_eq_cycled
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (skew : H →L[ℂ] H)
    (hleftSkew : Summable fun i =>
      ‖data.left (skew (sourceBasis i))‖ ^ 2) :
    TraceH sourceBasis ((data.traceProduct)† ∘L skew) =
      TraceG targetBasis ((data.left ∘L skew) ∘L data.right†) := by
  let forward : BasisHilbertSchmidtPairData (G := G) sourceBasis :=
    { left := data.right
      right := data.left ∘L skew
      left_summable_normSq := data.right_summable_normSq
      right_summable_normSq := hleftSkew }
  have hsource : forward.traceProduct =
      (data.traceProduct)† ∘L skew := by
    simp only [forward, BasisHilbertSchmidtPairData.traceProduct,
      BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have hforwardCycle : forward.right ∘L forward.left† =
      (data.left ∘L skew) ∘L data.right† := by
    rfl
  calc
    TraceH sourceBasis ((data.traceProduct)† ∘L skew) =
        TraceH sourceBasis forward.traceProduct := by
          rw [hsource]
    _ = TraceG targetBasis
        (forward.right ∘L forward.left†) :=
      forward.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
    _ = TraceG targetBasis
        ((data.left ∘L skew) ∘L data.right†) := by
      exact congrArg (TraceG targetBasis) hforwardCycle

theorem ordinaryTraceAlong_skew_comp_adjointPair_eq_cycled
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (skew : H →L[ℂ] H)
    (hleftAdjSkew : Summable fun i =>
      ‖data.right ((skew†) (sourceBasis i))‖ ^ 2) :
    TraceH sourceBasis (skew ∘L (data.traceProduct)†) =
      TraceG targetBasis (data.left ∘L skew ∘L data.right†) := by
  let reverse : BasisHilbertSchmidtPairData (G := G) sourceBasis :=
    { left := data.right ∘L skew†
      right := data.left
      left_summable_normSq := hleftAdjSkew
      right_summable_normSq := data.left_summable_normSq }
  have hsource : reverse.traceProduct =
      skew ∘L (data.traceProduct)† := by
    simp only [reverse, BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have hreverseCycle : reverse.right ∘L reverse.left† =
      data.left ∘L skew ∘L data.right† := by
    simp only [reverse, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  calc
    TraceH sourceBasis (skew ∘L (data.traceProduct)†) =
        TraceH sourceBasis reverse.traceProduct := by
          rw [hsource]
    _ = TraceG targetBasis
        (reverse.right ∘L reverse.left†) :=
      reverse.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
    _ = TraceG targetBasis
        (data.left ∘L skew ∘L data.right†) := by
      exact congrArg (TraceG targetBasis) hreverseCycle

/-! ## The signed two-suffix owner -/

theorem ordinaryTraceAlong_adjointPair_skewCoboundary_eq_cycledBoundaryDifference
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (oldData newData : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (skew : H →L[ℂ] H)
    (holdLeftSkew : Summable fun i =>
      ‖oldData.left (skew (sourceBasis i))‖ ^ 2)
    (hnewRightAdjSkew : Summable fun i =>
      ‖newData.right ((skew†) (sourceBasis i))‖ ^ 2) :
    TraceH sourceBasis
        ((oldData.traceProduct)† ∘L skew -
          skew ∘L (newData.traceProduct)†) =
      TraceG targetBasis
        ((oldData.left ∘L skew) ∘L oldData.right† -
          newData.left ∘L skew ∘L newData.right†) := by
  let oldForward : BasisHilbertSchmidtPairData (G := G) sourceBasis :=
    { left := oldData.right
      right := oldData.left ∘L skew
      left_summable_normSq := oldData.right_summable_normSq
      right_summable_normSq := holdLeftSkew }
  let newReverse : BasisHilbertSchmidtPairData (G := G) sourceBasis :=
    { left := newData.right ∘L skew†
      right := newData.left
      left_summable_normSq := hnewRightAdjSkew
      right_summable_normSq := newData.left_summable_normSq }
  let oldCycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := oldForward.right.adjoint
      right := oldForward.left.adjoint
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis oldForward.right holdLeftSkew
      right_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis oldForward.left
            oldData.right_summable_normSq }
  let newCycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := newReverse.right.adjoint
      right := newReverse.left.adjoint
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis newReverse.right
            newData.left_summable_normSq
      right_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis newReverse.left hnewRightAdjSkew }
  have holdSource : oldForward.traceProduct =
      (oldData.traceProduct)† ∘L skew := by
    simp only [oldForward, BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have hnewSource : newReverse.traceProduct =
      skew ∘L (newData.traceProduct)† := by
    simp only [newReverse, BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have holdTarget : oldCycled.traceProduct =
      (oldData.left ∘L skew) ∘L oldData.right† := by
    simp only [oldCycled, oldForward,
      BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_adjoint]
  have hnewTarget : newCycled.traceProduct =
      newData.left ∘L skew ∘L newData.right† := by
    simp only [newCycled, newReverse,
      BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have holdSourceTrace := oldForward.traceProduct_isTraceClassAlong
  have hnewSourceTrace := newReverse.traceProduct_isTraceClassAlong
  have holdTargetTrace := oldCycled.traceProduct_isTraceClassAlong
  have hnewTargetTrace := newCycled.traceProduct_isTraceClassAlong
  have holdCycleTrace :=
    oldForward.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
  have hnewCycleTrace :=
    newReverse.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
  have holdCycle : oldForward.right ∘L oldForward.left† =
      oldCycled.traceProduct := by
    rw [holdTarget]
  have hnewCycle : newReverse.right ∘L newReverse.left† =
      newCycled.traceProduct := by
    simp only [newReverse, newCycled,
      BasisHilbertSchmidtPairData.traceProduct,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  calc
    TraceH sourceBasis
        ((oldData.traceProduct)† ∘L skew -
          skew ∘L (newData.traceProduct)†) =
        TraceH sourceBasis ((oldData.traceProduct)† ∘L skew) -
          TraceH sourceBasis (skew ∘L (newData.traceProduct)†) := by
            apply ordinaryTraceAlong_sub sourceBasis
            · rw [← holdSource]
              exact holdSourceTrace
            · rw [← hnewSource]
              exact hnewSourceTrace
    _ = TraceH sourceBasis oldForward.traceProduct -
        TraceH sourceBasis newReverse.traceProduct := by
          rw [holdSource, hnewSource]
    _ = TraceG targetBasis oldCycled.traceProduct -
        TraceG targetBasis newCycled.traceProduct := by
          rw [holdCycleTrace, hnewCycleTrace, holdCycle, hnewCycle]
    _ = TraceG targetBasis
        (oldCycled.traceProduct - newCycled.traceProduct) := by
          rw [ordinaryTraceAlong_sub targetBasis _ _
            holdTargetTrace hnewTargetTrace]
    _ = TraceG targetBasis
        ((oldData.left ∘L skew) ∘L oldData.right† -
          newData.left ∘L skew ∘L newData.right†) := by
          rw [holdTarget, hnewTarget]

end CCM24FiniteSActualSchurTransitionSkewTrace
end CCM25Concrete
end Source
end ConnesWeilRH
