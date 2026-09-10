import ConnesWeilRH.Dev.C1G8AdjointShearGram

/-!
# G8 P1 ordinary-trace ledger

This leaf takes the already-formal P0 operator alignment to the same named
source-basis ordinary trace.  It retains the literal cutoff and records the
total forced complement as an owner-level operator; it does not identify a
finite-prime term or prove a limiting remainder estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1TraceLedger

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CC20Concrete.PositiveTrace
open C1G8AdjointShearGram
open Filter
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The three literal complement channels forced by the P0 source split. -/
noncomputable def g8P0ComplementOperator
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let J := sourceInclusion lambda
  let C := J† ∘L A
  let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
  C† ∘L J† ∘L g8AdjointShearGram owner lambda family ∘L D +
    D† ∘L g8AdjointShearGram owner lambda family ∘L J ∘L C +
      D† ∘L g8AdjointShearGram owner lambda family ∘L D

/-- P0 written using its named total complement operator. -/
theorem g8PhysicalEndpoint_traceProduct_eq_g8_add_internal_sub_complement
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct +
        ((g8SourceCutoffInternalCorrectionPairData owner lambda family globalBasis sourceBasis n).traceProduct -
          g8P0ComplementOperator owner lambda family globalBasis sourceBasis n) := by
  rw [g8SourceCutoffInternalCorrectionPairData_traceProduct_eq]
  simpa only [g8P0ComplementOperator] using
    (g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq_g8_add_internal_sub_complement
      owner lambda family globalBasis sourceBasis n)

/-- The total P0 complement is trace class because it is the exact difference
between the trace-class positive physical endpoint and the two traceable P0
terms.  This introduces no estimate or owner change. -/
theorem g8P0ComplementOperator_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8P0ComplementOperator owner lambda family globalBasis sourceBasis n) := by
  have hT := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct_isTraceClassAlong
  have hI := g8SourceCutoffInternalCorrectionPairData_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hP := g8PhysicalEndpointSourceCutoffPairData_traceProduct_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hsum := isTraceClassAlong_add sourceBasis _ _ hT hI
  have hEq : g8P0ComplementOperator owner lambda family globalBasis sourceBasis n =
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct +
        (g8SourceCutoffInternalCorrectionPairData owner lambda family globalBasis sourceBasis n).traceProduct -
          (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct := by
    rw [g8PhysicalEndpoint_traceProduct_eq_g8_add_internal_sub_complement]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    abel
  rw [hEq]
  exact isTraceClassAlong_sub sourceBasis _ _ hsum hP

/-- Exact same-owner ordinary-trace form of P0. -/
theorem ordinaryTraceAlong_g8PhysicalEndpoint_eq_g8_add_internal_sub_complement
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      ordinaryTraceAlong sourceBasis
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct +
        (ordinaryTraceAlong sourceBasis
          (g8SourceCutoffInternalCorrectionPairData owner lambda family globalBasis sourceBasis n).traceProduct -
          ordinaryTraceAlong sourceBasis
            (g8P0ComplementOperator owner lambda family globalBasis sourceBasis n)) := by
  rw [g8PhysicalEndpoint_traceProduct_eq_g8_add_internal_sub_complement]
  have hT := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct_isTraceClassAlong
  have hI := g8SourceCutoffInternalCorrectionPairData_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hC := g8P0ComplementOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hI_sub_C := isTraceClassAlong_sub sourceBasis _ _ hI hC
  rw [ordinaryTraceAlong_add sourceBasis _ _ hT hI_sub_C]
  rw [ordinaryTraceAlong_sub sourceBasis _ _ hI hC]

end
end C1G8P1TraceLedger
end Source
end ConnesWeilRH
