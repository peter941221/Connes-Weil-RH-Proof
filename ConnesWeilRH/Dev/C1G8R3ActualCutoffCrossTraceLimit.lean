/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3StrongTracePairTransfer
import ConnesWeilRH.Dev.C1G8R3PhysicalCutoffStrongLimit
import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Dev.C1G8P1EndpointOrientation

/-!
# Ordinary-trace limit for the actual G8 leakage/source cutoff channel

The physical output windows give a uniformly bounded source compression with
strongly convergent operators and adjoints. The existing same-owner
Hilbert--Schmidt pair transfer then gives ordinary-trace convergence for the
literal leakage/source channel. Its limit retains the global-convolution
compression and is not identified here with `qw`.
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
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.Dev.C1PositiveTraceWindowProducer
open Source.Dev.C1PositiveTraceCutoffAdapter
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricChannels
open Source.C1G8P1EndpointOrientation
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance actualCutoffSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The actual finite-window G8 factor compressed to the selected source
Sonin carrier. -/
noncomputable def g8SourceCompressedPhysicalCutoff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (n : ℕ) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L
    fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L
        sourceInclusion lambda

/-- The strong limit of the compressed physical cutoff. -/
noncomputable def g8SourceCompressedGlobalConvolution
    (lambda : CCM24SoninScale)
    (g : CompactLogConvolution.CompactLogTest) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L
    cc20GlobalLogConvolution g.involution.test ∘L sourceInclusion lambda

/-- Before taking any limit, the literal G8 leakage/source channel is the
source-band response sandwiched by the actual compressed physical cutoff.
This exposes the same-owner cutoff compatibility used in the trace limit. -/
theorem g8MetricCutoffLeakageSourceCrossOperator_eq_sourceBandSandwich
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : ℕ) :
    g8MetricCutoffLeakageSourceCrossOperator owner lambda family
        globalBasis sourceBasis n =
    (g8SourceCompressedPhysicalCutoff owner lambda n).adjoint ∘L
        (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
          g8SourceCompressedPhysicalCutoff owner lambda n := by
  let cutoffFactor := (sourceInclusion lambda).adjoint ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  have hcutoffFactor : cutoffFactor =
      g8SourceCompressedPhysicalCutoff owner lambda n := by
    simp [cutoffFactor, g8SourceCompressedPhysicalCutoff,
      g8SourceCutoffPairData, g8CutoffPairData,
      Source.Dev.C1Stage3ProjectionWindow.kernelSandwichPairData]
  calc
    _ = cutoffFactor.adjoint ∘L
          ((g8MetricLeakageCoframe lambda family).adjoint ∘L
            detectorOperator owner ∘L sourceInclusion lambda) ∘L cutoffFactor := by
      rw [g8MetricCutoffLeakageSourceCrossOperator_eq_literal_sandwich]
      apply ContinuousLinearMap.ext
      intro x
      rfl
    _ = (g8SourceCompressedPhysicalCutoff owner lambda n).adjoint ∘L
          (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
            g8SourceCompressedPhysicalCutoff owner lambda n := by
      rw [hcutoffFactor,
        g8MetricLeakageSourceCross_eq_neg_sourceBandGramResponse_adjoint]

/-- A uniformly bounded strongly convergent family and its adjoints have a
strongly convergent doubled product. -/
theorem tendsto_comp_adjoint_apply_of_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (cutoff : ℕ → H →L[ℂ] H) (limitCutoff : H →L[ℂ] H)
    (bound : ℝ)
    (hcutoff_norm : ∀ n, ‖cutoff n‖ ≤ bound)
    (hstrong : ∀ x,
      Tendsto (fun n => cutoff n x) atTop (𝓝 (limitCutoff x)))
    (hadjoint_strong : ∀ x,
      Tendsto (fun n => (cutoff n).adjoint x) atTop
        (𝓝 (limitCutoff.adjoint x)))
    (x : H) :
    Tendsto (fun n => cutoff n ((cutoff n).adjoint x)) atTop
      (𝓝 (limitCutoff (limitCutoff.adjoint x))) := by
  let difference : ℕ → H := fun n => (cutoff n).adjoint x - limitCutoff.adjoint x
  have hdifference : Tendsto difference atTop (𝓝 0) := by
    have h := (hadjoint_strong x).sub_const (limitCutoff.adjoint x)
    simpa [difference] using h
  have hdifference_norm : Tendsto (fun n => ‖difference n‖) atTop (𝓝 0) :=
    tendsto_norm_zero.comp hdifference
  have hmajor : Tendsto (fun n => bound * ‖difference n‖) atTop (𝓝 0) := by
    simpa using hdifference_norm.const_mul bound
  have herror_norm : Tendsto
      (fun n => ‖cutoff n (difference n)‖) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmajor
    · intro n
      exact norm_nonneg _
    · intro n
      calc
        ‖cutoff n (difference n)‖ ≤ ‖cutoff n‖ * ‖difference n‖ :=
          (cutoff n).le_opNorm _
        _ ≤ bound * ‖difference n‖ :=
          mul_le_mul_of_nonneg_right (hcutoff_norm n) (norm_nonneg _)
  have herror : Tendsto (fun n => cutoff n (difference n)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using herror_norm
  have hfixed : Tendsto (fun n => cutoff n (limitCutoff.adjoint x)) atTop
      (𝓝 (limitCutoff (limitCutoff.adjoint x))) :=
    hstrong (limitCutoff.adjoint x)
  have hsum := herror.add hfixed
  have hdecomp : (fun n => cutoff n ((cutoff n).adjoint x)) =
      (fun n => cutoff n (difference n) + cutoff n (limitCutoff.adjoint x)) := by
    funext n
    simp [difference, map_sub]
  rw [hdecomp]
  simpa using hsum

private theorem norm_kernelIntervalProjection_le_one
    (a c b : ℝ) : ‖kernelIntervalProjection a c b‖ ≤ (1 : ℝ) := by
  let E := kernelIntervalL2ZeroExtension a c b
  have hE : ‖E‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [E, one_mul] using (norm_kernelIntervalL2ZeroExtension a c b u).le
  have hEadj : ‖E.adjoint‖ ≤ (1 : ℝ) := by
    calc
      ‖E.adjoint‖ = ‖E‖ := ContinuousLinearMap.adjoint.norm_map E
      _ ≤ 1 := hE
  calc
    ‖kernelIntervalProjection a c b‖ = ‖E ∘L E.adjoint‖ := by
      simp [E, kernelIntervalProjection]
    _ ≤ ‖E‖ * ‖E.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hE hEadj (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem norm_g8SourceCompressedPhysicalCutoff_le_globalConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (n : ℕ) :
    ‖g8SourceCompressedPhysicalCutoff owner lambda n‖ ≤
      ‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ := by
  let J := sourceInclusion lambda
  let F := cc20GlobalLogConvolution owner.sourceTest.involution.test
  have hJ : ‖J‖ ≤ (1 : ℝ) := Submodule.norm_subtypeL_le _
  have hJadj : ‖J.adjoint‖ ≤ (1 : ℝ) := by
    calc
      ‖J.adjoint‖ = ‖J‖ := ContinuousLinearMap.adjoint.norm_map J
      _ ≤ 1 := hJ
  have hFcut : ‖fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)‖ ≤ ‖F‖ := by
    rw [fullBoundaryPositiveOperator_cutoff_eq_projection_comp_globalConvolution]
    let P := kernelIntervalProjection
      (-(cutoffUpper owner.sourceTest n))
      (-(cutoffLower owner.sourceTest n)) 0
    have hP : ‖P‖ ≤ (1 : ℝ) := by
      exact norm_kernelIntervalProjection_le_one _ _ _
    calc
      ‖P ∘L F‖ ≤ ‖P‖ * ‖F‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = ‖F‖ := one_mul _
  change ‖J.adjoint ∘L
      (fullBoundaryPositiveOperator owner.sourceTest
        (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L J)‖ ≤ ‖F‖
  calc
    ‖J.adjoint ∘L
        (fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L J)‖ ≤
      ‖J.adjoint‖ *
        ‖fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L J‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖J.adjoint‖ *
        (‖fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)‖ * ‖J‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖F‖ * 1) := by
      gcongr
    _ = ‖F‖ := by ring

/-- The compressed physical cutoff is uniformly bounded by the norm of the
fixed global convolution. -/
theorem g8SourceCompressedPhysicalCutoff_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (n : ℕ) :
    ‖g8SourceCompressedPhysicalCutoff owner lambda n‖ ≤
      ‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ := by
  exact norm_g8SourceCompressedPhysicalCutoff_le_globalConvolution owner lambda n

/-- The actual compressed cutoff and its adjoint converge strongly. -/
theorem tendsto_g8SourceCompressedPhysicalCutoff_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (u : sourceSoninCarrier lambda) :
    Tendsto (fun n => g8SourceCompressedPhysicalCutoff owner lambda n u) atTop
      (𝓝 (g8SourceCompressedGlobalConvolution lambda owner.sourceTest u)) := by
  simpa only [g8SourceCompressedPhysicalCutoff,
    g8SourceCompressedGlobalConvolution, ContinuousLinearMap.comp_apply] using
    tendsto_sourceCompressedPhysicalCutoff_apply lambda owner.sourceTest u

theorem tendsto_g8SourceCompressedPhysicalCutoff_adjoint_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (u : sourceSoninCarrier lambda) :
    Tendsto (fun n =>
      (g8SourceCompressedPhysicalCutoff owner lambda n).adjoint u) atTop
      (𝓝 ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint u)) := by
  simpa only [g8SourceCompressedPhysicalCutoff,
    g8SourceCompressedGlobalConvolution] using
    tendsto_sourceCompressedPhysicalCutoff_adjoint_apply lambda owner.sourceTest u

set_option maxHeartbeats 1000000 in
-- The full source-pair instantiation and dominated trace transfer need this budget.
/-- The literal G8 leakage/source trace converges under the actual expanding
physical windows. Its limit is the same-detector source response between two
global-convolution compressions. -/
theorem tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
          globalBasis sourceBasis n)) atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
          (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
            g8SourceCompressedGlobalConvolution lambda owner.sourceTest))) := by
  let cutoff : ℕ → sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedPhysicalCutoff owner lambda
  let limitCutoff : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedGlobalConvolution lambda owner.sourceTest
  let basePair := sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis sourceBasis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)
  let pair := basePair.swap.smulRight (-1)
  have hbasePair : basePair.traceProduct = sourceBandGramResponse owner lambda family := by
    exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis sourceBasis
      (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)
  have hpair : pair.traceProduct = -(sourceBandGramResponse owner lambda family).adjoint := by
    dsimp [pair]
    rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hbasePair]
    simp
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
  have hgeneric := tendsto_ordinaryTraceAlong_pairSandwich_of_strong
    sourceBasis boundaryBasis pair cutoff limitCutoff
      (‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ ^ 2)
      (sq_nonneg _) hdouble_norm hdouble
  have hchannel (n : ℕ) :
      g8MetricCutoffLeakageSourceCrossOperator owner lambda family
          globalBasis sourceBasis n =
        (cutoff n).adjoint ∘L pair.traceProduct ∘L cutoff n := by
    rw [g8MetricCutoffLeakageSourceCrossOperator_eq_sourceBandSandwich,
      ← hpair]
  have htraceSequence :
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
          globalBasis sourceBasis n)) =
      (fun n => ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich boundaryBasis (cutoff n).adjoint (cutoff n)).traceProduct)) := by
    funext n
    rw [hchannel n, pair.boundedSandwich_traceProduct_eq]
  have hchannelLimit :
      limitCutoff.adjoint ∘L pair.traceProduct ∘L limitCutoff =
        limitCutoff.adjoint ∘L
          (-(sourceBandGramResponse owner lambda family).adjoint) ∘L limitCutoff := by
    rw [hpair]
  rw [htraceSequence]
  convert hgeneric using 1
  apply congrArg (fun z : ℂ => 𝓝 z)
  rw [pair.boundedSandwich_traceProduct_eq, hchannelLimit]

end Dev
end ConnesWeilRH
