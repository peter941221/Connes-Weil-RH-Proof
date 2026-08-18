import ConnesWeilRH.Dev.C1PositiveTraceCutoffCompression

/-!
# C1 positive-trace cutoff obstruction

The diagonal majorant in a cutoff witness is a substantive analytic claim.
For the positive finite-window squares it implies a uniform upper bound on
the whole diagonal trace.  This file records the consequence so that a
future proof of trace growth can rule out the current whole-line dominated
cutoff interface directly.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffObstruction

open CC20Concrete
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem positiveComposition_trace_re_le_tsum_bound
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H)
    (operators : Nat → BasisHilbertSchmidtData basis)
    (bound : ι → ℝ) (hbound : Summable bound)
    (hdominated : ∀ n i,
      ‖⟪basis i,
        (operators n).positiveComposition (basis i)⟫_ℂ‖ ≤ bound i) (n : Nat) :
    (ordinaryTraceAlong basis
      (operators n).positiveComposition).re ≤ ∑' i, bound i := by
  have htraceSummable : Summable (fun i =>
      (⟪basis i, (operators n).positiveComposition (basis i)⟫_ℂ).re) :=
    Complex.reCLM.summable
      (BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong
        (operators n))
  have hterm : ∀ i,
      (⟪basis i, (operators n).positiveComposition (basis i)⟫_ℂ).re ≤ bound i := by
    intro i
    exact (le_abs_self _).trans
      ((Complex.abs_re_le_norm _).trans (hdominated n i))
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum
    (BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong
      (operators n))]
  exact htraceSummable.tsum_le_tsum hterm hbound

theorem cutoffDominatedTraceWitness_trace_re_le_bound_tsum
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis) (n : Nat) :
    (ordinaryTraceAlong globalBasis
      (cutoffPositiveBasisData g globalBasis n).positiveComposition).re ≤
      ∑' i, witness.bound i := by
  exact positiveComposition_trace_re_le_tsum_bound
    globalBasis
    (fun n => cutoffPositiveBasisData g globalBasis n)
    witness.bound witness.bound_summable witness.diagonal_dominated n

theorem cutoffDominatedTraceWitness_trace_re_bounded
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis) :
    ∃ boundValue : ℝ, ∀ n,
      (ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition).re ≤
        boundValue := by
  refine ⟨∑' i, witness.bound i, ?_⟩
  intro n
  exact cutoffDominatedTraceWitness_trace_re_le_bound_tsum
    g globalBasis witness n

/-- Once an actual lower-growth theorem is available, it immediately rules
out the current dominated-diagonal witness.  The lower-growth premise is
kept explicit because this module does not manufacture it from compact
support. -/
theorem not_exists_cutoffDominatedTraceWitness_of_trace_re_unbounded
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (hunbounded : ∀ boundValue : ℝ, ∃ n,
      boundValue <
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re) :
    ¬ Nonempty (CutoffDominatedTraceWitness g globalBasis) := by
  rintro ⟨witness⟩
  obtain ⟨n, hn⟩ := hunbounded (∑' i, witness.bound i)
  have hupper := cutoffDominatedTraceWitness_trace_re_le_bound_tsum
    g globalBasis witness n
  linarith

end

end C1PositiveTraceCutoffObstruction
end Dev
end Source
end ConnesWeilRH
