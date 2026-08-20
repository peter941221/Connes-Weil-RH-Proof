import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingKernel
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1CrossingCommonCarrierTransport

/-!
# C1CrossingCommonCarrier - one carrier for finitely many crossing traces

Stage 1 of the 1038 producer design (docs/proofs/1038).  The prime-power
crossing pair traces of one owner live on interval carriers
`Lp 2 (KernelInterval a c b)` that vary with `b`, while the positive-trace
family contract `PositiveTracePairLimitFamily` needs one Hilbert space and
one basis.  This module records the transport as a data-bearing contract:
a common carrier with, for every crossing length in a finite set, a pair
datum whose trace along the carrier basis equals the original interval
trace exactly.  The isometric construction of the carrier and the trace
preservation are producer obligations; the summation identity below is the
consumer side and is proved here unconditionally.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CrossingCommonCarrier

open MeasureTheory
open CC20Concrete.PositiveTrace
open CCM25Concrete.SelectedCrossingKernel
open CCM25Concrete.CompactLogConvolution
open C1CrossingCommonCarrierTransport
open scoped BigOperators

noncomputable section

universe u

/-- Common-carrier transport contract for the crossing pair traces of one
owner on a finite set of crossing lengths.  The carrier basis, the interval
bases, and the transported pair data are data; the two trace-preservation
fields are the producer obligation. -/
structure CrossingCommonCarrierData
    (h : ℝ → ℂ) (hh : Continuous h) (a c : ℝ) (S : Finset ℝ) where
  carrier : Type u
  [carrierGroup : NormedAddCommGroup carrier]
  [carrierInner : InnerProductSpace ℂ carrier]
  [carrierComplete : CompleteSpace carrier]
  target : Type u
  [targetGroup : NormedAddCommGroup target]
  [targetInner : InnerProductSpace ℂ target]
  [targetComplete : CompleteSpace target]
  carrierBasis : HilbertBasis ℕ ℂ carrier
  intervalBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))
  carrierPair : (b : ℝ) → BasisHilbertSchmidtPairData (G := target) carrierBasis
  carrierReversePair : (b : ℝ) → BasisHilbertSchmidtPairData (G := target)
      carrierBasis
  carrierPairTrace : (b : ℝ) → ℂ
  carrierReversePairTrace : (b : ℝ) → ℂ
  carrier_pair_trace_eq :
    ∀ b ∈ S, carrierPairTrace b =
      ordinaryTraceAlong carrierBasis (carrierPair b).traceProduct
  carrier_reverse_pair_trace_eq :
    ∀ b ∈ S, carrierReversePairTrace b =
      ordinaryTraceAlong carrierBasis (carrierReversePair b).traceProduct
  carrier_pair_trace :
    ∀ b ∈ S, carrierPairTrace b =
      ordinaryTraceAlong (intervalBasis b)
        (pairData h hh a c b (intervalBasis b)).traceProduct
  carrier_reverse_pair_trace :
    ∀ b ∈ S, carrierReversePairTrace b =
      ordinaryTraceAlong (intervalBasis b)
        (reversePairData h hh a c b (intervalBasis b)).traceProduct

/-- On a common carrier, the paired crossing traces of a finite set of
crossing lengths sum to the symmetric convolution-square values, exactly as
on the individual interval carriers.  This is the Stage-1 consumer identity:
no isometry has been constructed here, only the contract consumed. -/
theorem carrier_pair_trace_sum_eq_symmetric_convolutionSquare
    (g : CompactLogTest) (a c : ℝ) (S : Finset ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hS : ∀ b ∈ S, 0 ≤ b)
    (data : CrossingCommonCarrierData g.test g.test.continuous a c S) :
    ∑ b ∈ S,
        (data.carrierPairTrace b + data.carrierReversePairTrace b) =
      ∑ b ∈ S, (b : ℂ) *
        (g.convolutionSquare.test b + g.convolutionSquare.test (-b)) := by
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [data.carrier_pair_trace b hb, data.carrier_reverse_pair_trace b hb,
    pair_traces_add_eq_mul_symmetric_convolutionSquare g a c b hsupp (hS b hb)
      (data.intervalBasis b)]

/-- The crossing pair of length `b`, both legs transported through the two
basis-matching unitaries onto the common carrier (`KernelInterval a c b₀`
domain, `SourceInterval b₀` codomain).  Hilbert-Schmidt norms are preserved
because both unitaries are isometries matching bases. -/
noncomputable def carrierPairTransported
    (h : ℝ → ℂ) (hh : Continuous h) (a c b₀ : ℝ)
    (intervalBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (sourceBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (b : ℝ) :
    BasisHilbertSchmidtPairData (G := Lp ℂ 2 (volume : Measure (SourceInterval b₀)))
      (intervalBasis b₀) where
  left := ((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
      (pairData h hh a c b (intervalBasis b)).left).comp
      (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
  right := ((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
      (pairData h hh a c b (intervalBasis b)).right).comp
      (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
  left_summable_normSq := by
    have hn : ∀ n : ℕ,
        ‖((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
            (pairData h hh a c b (intervalBasis b)).left).comp
            (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
            (intervalBasis b₀ n)‖ ^ 2 =
          ‖(pairData h hh a c b (intervalBasis b)).left (intervalBasis b n)‖ ^ 2 := by
      intro n
      simp only [ContinuousLinearMap.comp_apply, basisMatchingCLM_basis,
        basisMatchingCLM_norm]
    exact (pairData h hh a c b (intervalBasis b)).left_summable_normSq.congr
      fun n => (hn n).symm
  right_summable_normSq := by
    have hn : ∀ n : ℕ,
        ‖((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
            (pairData h hh a c b (intervalBasis b)).right).comp
            (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
            (intervalBasis b₀ n)‖ ^ 2 =
          ‖(pairData h hh a c b (intervalBasis b)).right (intervalBasis b n)‖ ^ 2 := by
      intro n
      simp only [ContinuousLinearMap.comp_apply, basisMatchingCLM_basis,
        basisMatchingCLM_norm]
    exact (pairData h hh a c b (intervalBasis b)).right_summable_normSq.congr
      fun n => (hn n).symm

/-- The reverse crossing pair of length `b`, transported the same way. -/
noncomputable def carrierReversePairTransported
    (h : ℝ → ℂ) (hh : Continuous h) (a c b₀ : ℝ)
    (intervalBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (sourceBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (b : ℝ) :
    BasisHilbertSchmidtPairData (G := Lp ℂ 2 (volume : Measure (SourceInterval b₀)))
      (intervalBasis b₀) where
  left := ((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
      (reversePairData h hh a c b (intervalBasis b)).left).comp
      (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
  right := ((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
      (reversePairData h hh a c b (intervalBasis b)).right).comp
      (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
  left_summable_normSq := by
    have hn : ∀ n : ℕ,
        ‖((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
            (reversePairData h hh a c b (intervalBasis b)).left).comp
            (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
            (intervalBasis b₀ n)‖ ^ 2 =
          ‖(reversePairData h hh a c b (intervalBasis b)).left (intervalBasis b n)‖ ^ 2 := by
      intro n
      simp only [ContinuousLinearMap.comp_apply, basisMatchingCLM_basis,
        basisMatchingCLM_norm]
    exact (reversePairData h hh a c b (intervalBasis b)).left_summable_normSq.congr
      fun n => (hn n).symm
  right_summable_normSq := by
    have hn : ∀ n : ℕ,
        ‖((basisMatchingCLM (sourceBasis b) (sourceBasis b₀)).comp
            (reversePairData h hh a c b (intervalBasis b)).right).comp
            (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
            (intervalBasis b₀ n)‖ ^ 2 =
          ‖(reversePairData h hh a c b (intervalBasis b)).right (intervalBasis b n)‖ ^ 2 := by
      intro n
      simp only [ContinuousLinearMap.comp_apply, basisMatchingCLM_basis,
        basisMatchingCLM_norm]
    exact (reversePairData h hh a c b (intervalBasis b)).right_summable_normSq.congr
      fun n => (hn n).symm

/-- Stage-1b producer: the common-carrier contract is inhabited.  Given the
two basis families (never constructed in this repo), the carrier is the
`b₀`-interval space, and every crossing pair is transported through the
basis-matching unitaries with its trace preserved exactly. -/
noncomputable def crossingCommonCarrierData
    (h : ℝ → ℂ) (hh : Continuous h) (a c b₀ : ℝ) (S : Finset ℝ)
    (intervalBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (sourceBasis : (b : ℝ) → HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b)))) :
    CrossingCommonCarrierData h hh a c S where
  carrier := Lp ℂ 2 (volume : Measure (KernelInterval a c b₀))
  target := Lp ℂ 2 (volume : Measure (SourceInterval b₀))
  carrierBasis := intervalBasis b₀
  intervalBasis := intervalBasis
  carrierPair := fun b =>
    carrierPairTransported h hh a c b₀ intervalBasis sourceBasis b
  carrierReversePair := fun b =>
    carrierReversePairTransported h hh a c b₀ intervalBasis sourceBasis b
  carrierPairTrace := fun b =>
    ordinaryTraceAlong (intervalBasis b₀)
      (carrierPairTransported h hh a c b₀ intervalBasis sourceBasis b).traceProduct
  carrierReversePairTrace := fun b =>
    ordinaryTraceAlong (intervalBasis b₀)
      (carrierReversePairTransported h hh a c b₀ intervalBasis sourceBasis b).traceProduct
  carrier_pair_trace_eq := fun b _ => rfl
  carrier_reverse_pair_trace_eq := fun b _ => rfl
  carrier_pair_trace := by
    intro b _
    have hop : (carrierPairTransported h hh a c b₀ intervalBasis sourceBasis b).traceProduct =
        (((basisMatchingCLM (intervalBasis b₀) (intervalBasis b)).adjoint).comp
          (((pairData h hh a c b (intervalBasis b)).left).adjoint.comp
            (pairData h hh a c b (intervalBasis b)).right)).comp
        (basisMatchingCLM (intervalBasis b₀) (intervalBasis b)) :=
      conjPair_traceProduct
        (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
        (basisMatchingCLM (sourceBasis b₀) (sourceBasis b))
        (basisMatchingCLM (sourceBasis b) (sourceBasis b₀))
        (pairData h hh a c b (intervalBasis b)).left
        (pairData h hh a c b (intervalBasis b)).right
        (basisMatchingCLM_adjoint (sourceBasis b) (sourceBasis b₀))
        (fun z => basisMatchingCLM_cancel (sourceBasis b) (sourceBasis b₀) z)
    rw [hop]
    rw [ordinaryTraceAlong_conj_of_basisMatching (intervalBasis b₀)
      (intervalBasis b)
      (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
      (fun n => basisMatchingCLM_basis (intervalBasis b₀) (intervalBasis b) n)
      (((pairData h hh a c b (intervalBasis b)).left).adjoint.comp
        (pairData h hh a c b (intervalBasis b)).right)]
    rfl
  carrier_reverse_pair_trace := by
    intro b _
    have hop : (carrierReversePairTransported h hh a c b₀ intervalBasis sourceBasis b).traceProduct =
        (((basisMatchingCLM (intervalBasis b₀) (intervalBasis b)).adjoint).comp
          (((reversePairData h hh a c b (intervalBasis b)).left).adjoint.comp
            (reversePairData h hh a c b (intervalBasis b)).right)).comp
        (basisMatchingCLM (intervalBasis b₀) (intervalBasis b)) :=
      conjPair_traceProduct
        (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
        (basisMatchingCLM (sourceBasis b₀) (sourceBasis b))
        (basisMatchingCLM (sourceBasis b) (sourceBasis b₀))
        (reversePairData h hh a c b (intervalBasis b)).left
        (reversePairData h hh a c b (intervalBasis b)).right
        (basisMatchingCLM_adjoint (sourceBasis b) (sourceBasis b₀))
        (fun z => basisMatchingCLM_cancel (sourceBasis b) (sourceBasis b₀) z)
    rw [hop]
    rw [ordinaryTraceAlong_conj_of_basisMatching (intervalBasis b₀)
      (intervalBasis b)
      (basisMatchingCLM (intervalBasis b₀) (intervalBasis b))
      (fun n => basisMatchingCLM_basis (intervalBasis b₀) (intervalBasis b) n)
      (((reversePairData h hh a c b (intervalBasis b)).left).adjoint.comp
        (reversePairData h hh a c b (intervalBasis b)).right)]
    rfl

end
end C1CrossingCommonCarrier
end Source
end ConnesWeilRH
