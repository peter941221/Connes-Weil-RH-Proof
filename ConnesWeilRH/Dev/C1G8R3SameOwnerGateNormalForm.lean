/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit

/-!
# The ρ5 same-owner gate as one normal form

Record 1500 isolated the substantive gate of the G8 same-owner readback:
given the two formal channel limits and the endpoint limit, the readback
contract holds exactly when the aggregate limit value equals
`Source.C1SameOwnerWeil.qw owner.sourceTest`.  This file makes that
isolation a theorem.  With the endpoint brick
(`C1G8R3ActualEndpointTraceLimit`) the full readback trace converges to
the named aggregate limit operator as soon as the survivor core square-sum
holds, and the gate collapses to ONE real equation.  Consequences:

* forward: from ANY `G8SameOwnerReadbackData` (arbitrary remainder) plus
  the survivor core, the aggregate limit value equals `qw` — necessity;
* backward: that one equation CONSTRUCTS a zero-remainder
  `G8SameOwnerReadbackData` — sufficiency, feeding the committed
  positive-trace consumer unchanged.

The only estimate-shaped premise is the survivor core square-sum; no
`qw` sign is ever an input (record-012 typed-circularity stop rule, record
1501 packaging checklist).  The identification itself is NOT proved: RH is
not touched.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.Dev.C1PositiveTraceCutoffAdapter
open Source.Dev.C1PositiveTraceWindowProducer
open Source.Dev.C1PositiveTraceTraceContinuity
open Source.C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance sameOwnerGateSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The real readback trace `t_n` of record 1500, as a named function. -/
noncomputable def g8ReadbackRealTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (n : Nat) : Real :=
  (ordinaryTraceAlong sourceBasis
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re

/-- Under the survivor core, the real readback trace converges to the real
part of the aggregate endpoint limit value. -/
theorem tendsto_g8ReadbackRealTrace_of_survivorCore
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2) :
    Tendsto (g8ReadbackRealTrace owner lambda family globalBasis sourceBasis)
      atTop
      (𝓝 ((ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffLimitOperator owner lambda family)).re)) := by
  have hcx := tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore
    owner lambda family globalBasis sourceBasis hcore
  have hstep : Tendsto
      (fun n : ℕ =>
        (ordinaryTraceAlong sourceBasis
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re)
      atTop
      (𝓝 ((ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffLimitOperator owner lambda family)).re)) :=
    (Complex.continuous_re.tendsto
      (ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffLimitOperator owner lambda family))).comp hcx
  exact hstep

/-- **The ρ5 gate as one equivalence.**  Given the survivor core, the
unremaindered readback converges to `qw` exactly when the aggregate limit
value equals `qw`.  This is the substantive gate of record 1500 equation
(3); nothing here proves it. -/
theorem g8R5_readbackTendsto_iff_aggregateLimit_eq_qw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2) :
    Tendsto (fun n : ℕ =>
        (ordinaryTraceAlong sourceBasis
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re)
      atTop (𝓝 (Source.C1SameOwnerWeil.qw owner.sourceTest))
      ↔ ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
          = Source.C1SameOwnerWeil.qw owner.sourceTest) := by
  have hlim := tendsto_g8ReadbackRealTrace_of_survivorCore owner lambda family
    globalBasis sourceBasis hcore
  constructor
  · intro hqw
    have hfold :
        (fun n : ℕ =>
            (ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re) =
          g8ReadbackRealTrace owner lambda family globalBasis sourceBasis :=
      rfl
    rw [hfold] at hqw
    exact tendsto_nhds_unique hlim hqw
  · intro heq
    rw [← heq]
    have hfold :
        (fun n : ℕ =>
            (ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re) =
          g8ReadbackRealTrace owner lambda family globalBasis sourceBasis :=
      rfl
    rw [hfold]
    exact hlim

/-- Sufficiency direction, packaged: the aggregate-limit equation CONSTRUCTS
a zero-remainder same-owner readback data, feeding the committed
positive-trace consumer unchanged. -/
noncomputable def g8R5ZeroRemainderReadbackData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2)
    (heq : (ordinaryTraceAlong sourceBasis
          (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
        = Source.C1SameOwnerWeil.qw owner.sourceTest) :
    G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis where
  remainder := fun _ => (0 : Real)
  remainder_tendsto_zero := tendsto_const_nhds
  readback_tendsto_qw := by
    have hfn :
        (fun n : ℕ =>
            (ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re -
              (fun _ : ℕ => (0 : Real)) n) =
          (fun n : ℕ =>
            (ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re) :=
      funext fun n => by simp
    rw [hfn, ← heq]
    exact tendsto_g8ReadbackRealTrace_of_survivorCore owner lambda family
      globalBasis sourceBasis hcore

/-- Necessity direction: from ANY same-owner readback data (arbitrary
remainder) plus the survivor core, the aggregate limit value equals `qw`.
No estimate is used; only limit algebra. -/
theorem g8R5_aggregateLimit_eq_qw_of_sameOwnerReadbackData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2)
    (data : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis) :
    (ordinaryTraceAlong sourceBasis
          (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
        = Source.C1SameOwnerWeil.qw owner.sourceTest := by
  have hlim := tendsto_g8ReadbackRealTrace_of_survivorCore owner lambda family
    globalBasis sourceBasis hcore
  have hfold :
      (fun n : ℕ =>
          (ordinaryTraceAlong sourceBasis
            (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re) =
        g8ReadbackRealTrace owner lambda family globalBasis sourceBasis :=
    rfl
  have hpt :
      (fun n : ℕ =>
          (ordinaryTraceAlong sourceBasis
            (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re) =
        (fun n : ℕ =>
          ((ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re -
            data.remainder n) + data.remainder n) :=
    funext fun n => by ring
  have hlim2 : Tendsto
      (fun n : ℕ =>
        ((ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re -
            data.remainder n) + data.remainder n)
      atTop
      (𝓝 ((ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffLimitOperator owner lambda family)).re)) := by
    rw [← hpt]
    exact hlim
  have hsplit : Tendsto
      (fun n : ℕ =>
        ((ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re -
            data.remainder n) + data.remainder n)
      atTop (𝓝 (Source.C1SameOwnerWeil.qw owner.sourceTest + 0)) :=
    data.readback_tendsto_qw.add data.remainder_tendsto_zero
  have hsum : Tendsto
      (fun n : ℕ =>
        ((ordinaryTraceAlong sourceBasis
              (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re -
            data.remainder n) + data.remainder n)
      atTop (𝓝 (Source.C1SameOwnerWeil.qw owner.sourceTest)) := by
    simpa only [add_zero] using hsplit
  exact tendsto_nhds_unique hlim2 hsum

end Dev
end ConnesWeilRH
