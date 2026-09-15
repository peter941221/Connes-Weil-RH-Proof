/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffCrossTraceLimit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder

/-!
# Actual G8 cutoff limit for the same-owner signed endpoint remainder

The actual source-compressed physical G8 cutoff converges through the fixed
Hilbert--Schmidt pair that owns the signed first-jet remainder.  This gives a
same-owner ordinary-trace limit for the cutoff remainder sandwich.  It does
not assert that the limit vanishes or that the full G8 metric reads back to
`qw`.
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
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance actualRemainderCutoffSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
-- The actual cutoff and paired-boundary basis transport need this budget.
/-- The same-owner signed finite-Euler remainder has an ordinary-trace limit
under the actual expanding physical G8 windows. -/
theorem tendsto_ordinaryTraceAlong_sourceActualBandFiniteEulerRemainder_actualCutoff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedPhysicalCutoff owner lambda n).adjoint ∘L
          sourceActualBandFiniteEulerRemainderResponse owner lambda family ∘L
            g8SourceCompressedPhysicalCutoff owner lambda n))
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
          sourceActualBandFiniteEulerRemainderResponse owner lambda family ∘L
            g8SourceCompressedGlobalConvolution lambda owner.sourceTest))) := by
  let cutoff : ℕ → sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedPhysicalCutoff owner lambda
  let limitCutoff : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedGlobalConvolution lambda owner.sourceTest
  let firstPair := sourceActualBandFiniteEulerSoninPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis hfactor
  let bandPair := sourceThreeBranchSourcePairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  have hfirstPair : firstPair.traceProduct =
      sourceActualBandFiniteEulerSoninResponse owner lambda family := by
    exact sourceActualBandFiniteEulerSoninPairData_traceProduct_eq owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hbandPair : bandPair.traceProduct =
      sourceBandGramResponse owner lambda family := by
    exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hcutoff_bound : ∀ n, ‖cutoff n‖ ≤ ‖cc20GlobalLogConvolution
      owner.sourceTest.involution.test‖ := by
    intro n
    exact g8SourceCompressedPhysicalCutoff_norm_le owner lambda n
  have hcutoff_strong : ∀ x,
      Tendsto (fun n => cutoff n x) atTop (𝓝 (limitCutoff x)) := by
    intro x
    exact tendsto_g8SourceCompressedPhysicalCutoff_apply owner lambda x
  have hadjoint_strong : ∀ x,
      Tendsto (fun n => (cutoff n).adjoint x) atTop
        (𝓝 (limitCutoff.adjoint x)) := by
    intro x
    exact tendsto_g8SourceCompressedPhysicalCutoff_adjoint_apply owner lambda x
  have hdouble := tendsto_comp_adjoint_apply_of_strong cutoff limitCutoff
    ‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖
    hcutoff_bound hcutoff_strong hadjoint_strong
  have hdouble_norm : ∀ n,
      ‖cutoff n ∘L (cutoff n).adjoint‖ ≤
        ‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ ^ 2 := by
    intro n
    calc
      ‖cutoff n ∘L (cutoff n).adjoint‖ ≤
          ‖cutoff n‖ * ‖(cutoff n).adjoint‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖cutoff n‖ ^ 2 := by
        rw [show ‖(cutoff n).adjoint‖ = ‖cutoff n‖ from
          ContinuousLinearMap.adjoint.norm_map (cutoff n)]
        ring
      _ ≤ ‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hcutoff_bound n)
  have hfirstGeneric := tendsto_ordinaryTraceAlong_pairSandwich_of_strong
    sourceBasis pairedBoundaryBasis firstPair cutoff limitCutoff
      (‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ ^ 2)
      (sq_nonneg _) hdouble_norm hdouble
  have hbandGeneric := tendsto_ordinaryTraceAlong_pairSandwich_of_strong
    sourceBasis boundaryBasis bandPair cutoff limitCutoff
      (‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ ^ 2)
      (sq_nonneg _) hdouble_norm hdouble
  have hfirstTraceSequence :
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L
          sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L cutoff n)) =
      (fun n => ordinaryTraceAlong sourceBasis
        ((firstPair.boundedSandwich pairedBoundaryBasis (cutoff n).adjoint
          (cutoff n)).traceProduct)) := by
    funext n
    rw [firstPair.boundedSandwich_traceProduct_eq, hfirstPair]
  have hbandTraceSequence :
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n)) =
      (fun n => ordinaryTraceAlong sourceBasis
        ((bandPair.boundedSandwich boundaryBasis (cutoff n).adjoint
          (cutoff n)).traceProduct)) := by
    funext n
    rw [bandPair.boundedSandwich_traceProduct_eq, hbandPair]
  have hfirst : Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L
          sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L cutoff n))
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        (limitCutoff.adjoint ∘L
          sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L
            limitCutoff))) := by
    rw [hfirstTraceSequence]
    have hlimit :
        ordinaryTraceAlong sourceBasis
          (limitCutoff.adjoint ∘L
            sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L limitCutoff) =
          ordinaryTraceAlong sourceBasis
            ((firstPair.boundedSandwich pairedBoundaryBasis limitCutoff.adjoint
              limitCutoff).traceProduct) := by
      rw [firstPair.boundedSandwich_traceProduct_eq, hfirstPair]
    rw [hlimit]
    exact hfirstGeneric
  have hband : Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n))
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L
          limitCutoff))) := by
    rw [hbandTraceSequence]
    have hlimit :
        ordinaryTraceAlong sourceBasis
          (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L
            limitCutoff) =
          ordinaryTraceAlong sourceBasis
            ((bandPair.boundedSandwich boundaryBasis limitCutoff.adjoint
              limitCutoff).traceProduct) := by
      rw [bandPair.boundedSandwich_traceProduct_eq, hbandPair]
    rw [hlimit]
    exact hbandGeneric
  have hfirstTraceClass (n : ℕ) :
      IsTraceClassAlong sourceBasis
        ((cutoff n).adjoint ∘L
      sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L cutoff n) := by
    rw [← hfirstPair]
    exact firstPair.boundedSandwich_isTraceClassAlong pairedBoundaryBasis
      (cutoff n).adjoint (cutoff n)
  have hbandTraceClass (n : ℕ) :
      IsTraceClassAlong sourceBasis
        ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n) := by
    rw [← hbandPair]
    exact bandPair.boundedSandwich_isTraceClassAlong boundaryBasis
      (cutoff n).adjoint (cutoff n)
  have hoperatorSub (n : ℕ) :
      (cutoff n).adjoint ∘L
          sourceActualBandFiniteEulerRemainderResponse owner lambda family ∘L cutoff n =
        ((cutoff n).adjoint ∘L
          sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L cutoff n) -
          ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n) := by
    rw [sourceActualBandFiniteEulerRemainderResponse]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  have hsequence :
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L
          sourceActualBandFiniteEulerRemainderResponse owner lambda family ∘L cutoff n)) =
      (fun n => ordinaryTraceAlong sourceBasis
          ((cutoff n).adjoint ∘L
            sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L cutoff n) -
        ordinaryTraceAlong sourceBasis
          ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n)) := by
    funext n
    rw [hoperatorSub n, ordinaryTraceAlong_sub sourceBasis _ _
      (hfirstTraceClass n) (hbandTraceClass n)]
  have hlimitTraceClassFirst :
      IsTraceClassAlong sourceBasis
        (limitCutoff.adjoint ∘L
          sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L limitCutoff) := by
    rw [← hfirstPair]
    exact firstPair.boundedSandwich_isTraceClassAlong pairedBoundaryBasis
      limitCutoff.adjoint limitCutoff
  have hlimitTraceClassBand :
      IsTraceClassAlong sourceBasis
        (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L limitCutoff) := by
    rw [← hbandPair]
    exact bandPair.boundedSandwich_isTraceClassAlong boundaryBasis
      limitCutoff.adjoint limitCutoff
  have hlimitSub :
      ordinaryTraceAlong sourceBasis
        (limitCutoff.adjoint ∘L
          sourceActualBandFiniteEulerRemainderResponse owner lambda family ∘L limitCutoff) =
        ordinaryTraceAlong sourceBasis
          (limitCutoff.adjoint ∘L
            sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L limitCutoff) -
          ordinaryTraceAlong sourceBasis
            (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L limitCutoff) := by
    rw [sourceActualBandFiniteEulerRemainderResponse]
    have hoperator :
        limitCutoff.adjoint ∘L
            (sourceActualBandFiniteEulerSoninResponse owner lambda family -
              sourceBandGramResponse owner lambda family) ∘L limitCutoff =
          (limitCutoff.adjoint ∘L
              sourceActualBandFiniteEulerSoninResponse owner lambda family ∘L limitCutoff) -
            (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L limitCutoff) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    rw [hoperator, ordinaryTraceAlong_sub sourceBasis _ _
      hlimitTraceClassFirst hlimitTraceClassBand]
  rw [hsequence, hlimitSub]
  exact hfirst.sub hband

end Dev
end ConnesWeilRH
