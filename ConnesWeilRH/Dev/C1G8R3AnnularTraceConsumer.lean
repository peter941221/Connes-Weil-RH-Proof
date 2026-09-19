/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SourceRootFiniteWindowCriterion

/-!
# Trace-form consumer for the uniform annular Gram bound

After the trace-class upgrade and the annular trace positivity result, the
natural statement of the single remaining S3 producer is the ordered estimate

```text
0 <= Re tr Gram(N,n) <= B     uniformly for n >= N.
```

The existing survivor-core square-sum consumers accept only the
column-energy form (a bound on `∑' i, ‖window (basis i)‖^2`).  This module
closes that interface: a uniform trace bound is transported through the exact
column-energy identity to the tsum form, and then dispatched to the ambient
and compressed square-sum consumers.  The uniform annular Gram upper bound
can therefore be stated, proved, and consumed entirely at trace level.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped Topology

/-! ### Ambient annular form -/

theorem sourceRootAnnularGram_column_energy_tsum_le_of_trace_le
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hn : selectedRootSupportRadius owner ≤ (n : ℝ)) {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    {B : ℝ}
    (htrace : (Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong
      sourceBasis (sourceRootAnnularGram owner lambda N n)).re ≤ B) :
    (∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
      (sourceBasis i)‖ ^ 2) ≤ B := by
  have htrace' := htrace
  have hs := sourceRootAnnularOutputWindow_sourceBasis_normSq_summable
    owner lambda N n hN hn sourceBasis
  have hcast : (∑' i, ((‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 : ℝ) : ℂ)) =
      ((∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.ofRealCLM.map_tsum hs).symm
  rw [sourceRootAnnularGram_trace_eq_column_energy owner lambda N n sourceBasis,
    hcast, Complex.ofReal_re] at htrace'
  exact htrace'

/-! ### Compressed annular form -/

theorem sourceCompressedRootAnnularGram_column_energy_tsum_le_of_trace_le
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hn : selectedRootSupportRadius owner ≤ (n : ℝ)) {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    {B : ℝ}
    (htrace : (Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong
      sourceBasis (sourceCompressedRootAnnularGram owner lambda N n)).re ≤ B) :
    (∑' i, ‖sourceCompressedRootAnnularWindow owner lambda N n
      (sourceBasis i)‖ ^ 2) ≤ B := by
  have htrace' := htrace
  have hs := sourceCompressedRootAnnularWindow_sourceBasis_normSq_summable
    owner lambda N n hN hn sourceBasis
  have hcast : (∑' i, ((‖sourceCompressedRootAnnularWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 : ℝ) : ℂ)) =
      ((∑' i, ‖sourceCompressedRootAnnularWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.ofRealCLM.map_tsum hs).symm
  rw [sourceCompressedRootAnnularGram_trace_eq_column_energy
      owner lambda N n sourceBasis,
    hcast, Complex.ofReal_re] at htrace'
  exact htrace'

/-! ### The trace-form survivor-core consumers -/

/-- A uniform upper bound on the real part of the ambient annular Gram trace
implies the survivor-core square-sum.  This is the trace-level analogue of
`sourceCompressedRoot_squareSum_of_eventual_ambient_annular_tsum_energy`. -/
theorem sourceCompressedRoot_squareSum_of_eventual_ambient_annular_trace_bound
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    {B : ℝ}
    (htrace : ∀ n, N ≤ n →
      (Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceRootAnnularGram owner lambda N n)).re ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  refine sourceCompressedRoot_squareSum_of_eventual_ambient_annular_tsum_energy
    owner lambda sourceBasis N hN (B := B) ?_
  intro n hn
  exact sourceRootAnnularGram_column_energy_tsum_le_of_trace_le
    owner lambda N n hN (le_trans hN (Nat.cast_le.mpr hn)) sourceBasis
    (htrace n hn)

/-- A uniform upper bound on the real part of the compressed annular Gram
trace implies the survivor-core square-sum.  This is the trace-level
analogue of `sourceCompressedRoot_squareSum_of_eventual_annular_tsum_energy`. -/
theorem sourceCompressedRoot_squareSum_of_eventual_annular_trace_bound
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    {B : ℝ}
    (htrace : ∀ n, N ≤ n →
      (Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceCompressedRootAnnularGram owner lambda N n)).re ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  refine sourceCompressedRoot_squareSum_of_eventual_annular_tsum_energy
    owner lambda sourceBasis N hN (B := B) ?_
  intro n hn
  exact sourceCompressedRootAnnularGram_column_energy_tsum_le_of_trace_le
    owner lambda N n hN (le_trans hN (Nat.cast_le.mpr hn)) sourceBasis
    (htrace n hn)

end Dev
end ConnesWeilRH
