/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3DiagonalRootLegNormalForm

/-!
# Necessary energy bound for a finite G8 diagonal trace limit

If the actual-cutoff diagonal trace has a finite limit, pointwise convergence
of its selected detector-root columns forces the uncut same-owner columns to
be square-summable. This isolates the uniform energy estimate still needed
for the diagonal G8 channels.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.Dev.C1Stage3ProjectionWindow
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricChannels
open Filter
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance diagonalRootConstraintSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The uncut same-owner selected detector-root leg for one diagonal G8
coframe. -/
noncomputable def g8MetricGlobalDetectorRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L leg ∘L
    g8SourceCompressedGlobalConvolution lambda owner.sourceTest

/-- The actual finite-cutoff detector-root columns converge pointwise to the
uncut same-owner columns. -/
theorem tendsto_g8MetricCutoffDetectorRootLeg_apply
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) (i : ρ) :
    Tendsto
      (fun n => g8MetricCutoffDetectorRootLeg owner lambda family globalBasis
        sourceBasis n leg (sourceBasis i)) atTop
      (𝓝 (g8MetricGlobalDetectorRootLeg owner lambda leg (sourceBasis i))) := by
  let cutoff : ℕ → sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedPhysicalCutoff owner lambda
  have hcutoff : Tendsto (fun n => cutoff n (sourceBasis i)) atTop
      (𝓝 (g8SourceCompressedGlobalConvolution lambda owner.sourceTest
        (sourceBasis i))) := by
    exact tendsto_g8SourceCompressedPhysicalCutoff_apply owner lambda (sourceBasis i)
  have hroot := (ContinuousLinearMap.continuous
    (rootConvolution owner ∘L leg)).continuousAt.tendsto.comp hcutoff
  have hC (n : ℕ) :
      (sourceInclusion lambda).adjoint ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left =
      cutoff n := by
    simp [cutoff, g8SourceCompressedPhysicalCutoff, g8SourceCutoffPairData,
      g8CutoffPairData,
      Source.Dev.C1Stage3ProjectionWindow.kernelSandwichPairData]
  simpa only [g8MetricCutoffDetectorRootLeg, g8MetricGlobalDetectorRootLeg,
    ContinuousLinearMap.coe_comp', Function.comp_apply, hC,
    ContinuousLinearMap.comp_apply] using hroot

/-- A finite real limit for an actual-cutoff diagonal trace forces the
uncut detector-root columns to have finite total energy on the same source
basis. The theorem records a necessary condition; it does not assert the
limit or supply the missing energy estimate. -/
theorem summable_normSq_g8MetricGlobalDetectorRootLeg_of_tendsto_diagonal_trace_re
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    {L : ℝ}
    (htrace : Tendsto
      (fun n => (ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          leg leg)).re) atTop (𝓝 L)) :
    Summable (fun i =>
      ‖g8MetricGlobalDetectorRootLeg owner lambda leg (sourceBasis i)‖ ^ 2) := by
  let rootLeg := fun n =>
    g8MetricCutoffDetectorRootLeg owner lambda family globalBasis sourceBasis n leg
  let globalRootLeg := g8MetricGlobalDetectorRootLeg owner lambda leg
  have hcolumn : ∀ i,
      Tendsto (fun n => ‖rootLeg n (sourceBasis i)‖ ^ 2) atTop
        (𝓝 (‖globalRootLeg (sourceBasis i)‖ ^ 2)) := by
    intro i
    have hpoint := tendsto_g8MetricCutoffDetectorRootLeg_apply owner lambda family
      globalBasis sourceBasis leg i
    exact ((continuous_norm.pow 2).continuousAt.tendsto.comp hpoint)
  have htrace_energy (n : ℕ) :
      (ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          leg leg)).re = ∑' i, ‖rootLeg n (sourceBasis i)‖ ^ 2 := by
    rw [ordinaryTraceAlong_g8MetricCutoffDiagonal_eq_rootLeg_energy]
    simp [rootLeg, Complex.ofReal_re]
  have hfinite_bound (s : Finset ρ) :
      ∑ i ∈ s, ‖globalRootLeg (sourceBasis i)‖ ^ 2 ≤ L := by
    have hfinite_tendsto :
        Tendsto (fun n => ∑ i ∈ s, ‖rootLeg n (sourceBasis i)‖ ^ 2) atTop
          (𝓝 (∑ i ∈ s, ‖globalRootLeg (sourceBasis i)‖ ^ 2)) := by
      exact tendsto_finsetSum s (fun i _ => hcolumn i)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    apply le_of_tendsto hfinite_tendsto
    filter_upwards [Metric.tendsto_nhds.1 htrace ε hε] with n hn
    have htrace_le :
        (ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            leg leg)).re ≤ L + ε := by
      rw [Real.dist_eq] at hn
      have habs : |(ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            leg leg)).re - L| < ε := by simpa using hn
      linarith [abs_lt.mp habs]
    calc
      ∑ i ∈ s, ‖rootLeg n (sourceBasis i)‖ ^ 2 ≤
          (ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              leg leg)).re := by
        rw [htrace_energy n]
        have hsum := PositiveTrace.summable_normSq_of_isTraceClassAlong_adjoint_comp_self
          sourceBasis (rootLeg n) (by
            rw [← g8MetricCutoffDiagonalChannel_eq_rootLeg_square owner lambda
              family globalBasis sourceBasis n leg]
            exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family
              globalBasis sourceBasis n leg leg)
        exact hsum.sum_le_tsum s (fun i _ => sq_nonneg _)
      _ ≤ L + ε := htrace_le
  exact summable_of_sum_le (fun i => sq_nonneg _) hfinite_bound

end Dev
end ConnesWeilRH
