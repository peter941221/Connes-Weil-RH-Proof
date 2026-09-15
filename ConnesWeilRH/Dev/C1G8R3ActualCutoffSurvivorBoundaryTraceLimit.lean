/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffSurvivorBoundaryPair
import ConnesWeilRH.Dev.C1G8R3ActualCutoffCrossTraceLimit
import ConnesWeilRH.Dev.C1G8R3StrongTracePairTransfer
import ConnesWeilRH.Dev.C1G8P1BoundaryOrthogonality
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPolarTraceBridge
import ConnesWeilRH.Dev.C1G8AdjointShearGram

/-!
# Same-owner survivor/boundary trace limit for the actual cutoff

The survivor and visible-boundary ranges split across the same source Sonin
projection. Their mixed detector corner is therefore a compression of its
commutator. The existing three-branch Hilbert--Schmidt pair supplies one
fixed trace owner, so the actual physical cutoff has an ordinary-trace limit.
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
open Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
open Source.CCM25Concrete.CCM24FiniteSSchurMarkovPolarTraceBridge
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.C1G8P1MetricChannels
open Source.C1G8P1BoundaryOrthogonality
open Source.C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance survivorBoundaryTraceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem emptyPolarFrame_comp_adjoint_eq_sourceSoninProjection
    (lambda : CCM24SoninScale) :
    newSuffixFrame lambda [] ∘L (newSuffixFrame lambda []).adjoint =
      sourceSoninProjection lambda := by
  let J := sourceInclusion lambda
  let Z := suffixEulerEmptyPolarSimilarity lambda
  have hZ : Z ∘L Z = ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) :=
    suffixEulerEmptyPolarSimilarity_comp_self lambda
  have hZadj : Z.adjoint = Z :=
    (suffixEulerEmptyPolarSimilarity_isSelfAdjoint lambda).adjoint_eq
  have hJJ := sourceInclusion_comp_adjoint lambda
  rw [newSuffixFrame_nil_eq_sourceInclusion_comp_emptySimilarity]
  rw [ContinuousLinearMap.adjoint_comp, hZadj]
  change (J ∘L Z) ∘L (Z ∘L J.adjoint) = sourceSoninProjection lambda
  calc
    (J ∘L Z) ∘L (Z ∘L J.adjoint) =
        J ∘L ((Z ∘L Z) ∘L J.adjoint) := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = J ∘L J.adjoint := by rw [hZ]; simp
    _ = sourceSoninProjection lambda := hJJ

private theorem sourceSoninProjection_comp_g8MetricSurvivor_eq
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L g8MetricSurvivorCoframe lambda family =
      g8MetricSurvivorCoframe lambda family := by
  let F := newSuffixFrame lambda []
  have hFiso : F.adjoint ∘L F =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [F, newSuffixFrame] using
      parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 [] (by norm_num)
  have hFproj : F ∘L F.adjoint = sourceSoninProjection lambda := by
    simpa only [F] using emptyPolarFrame_comp_adjoint_eq_sourceSoninProjection lambda
  have hPF : sourceSoninProjection lambda ∘L F = F := by
    rw [← hFproj]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hx := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => F (T x)) hFiso
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hx
  have hPFpoint (y : sourceSoninCarrier lambda) :
      sourceSoninProjection lambda (F y) = F y :=
    DFunLike.congr_fun hPF y
  apply ContinuousLinearMap.ext
  intro x
  simp only [g8MetricSurvivorCoframe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]
  rw [hPFpoint]

private theorem sourceSoninProjection_comp_g8MetricVisibleBoundary_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L g8MetricVisibleBoundaryCoframe lambda family = 0 := by
  let F := newSuffixFrame lambda []
  have hFproj : F ∘L F.adjoint = sourceSoninProjection lambda := by
    simpa only [F] using emptyPolarFrame_comp_adjoint_eq_sourceSoninProjection lambda
  have horth : F.adjoint ∘L g8MetricVisibleBoundaryCoframe lambda family = 0 := by
    simpa only [F] using
      suffixEulerTerminalFrame_adjoint_comp_g8MetricVisibleBoundaryCoframe_eq_zero
        lambda family
  rw [← hFproj, ContinuousLinearMap.comp_assoc, horth]
  simp

/-- The same-detector commutator pair, precomposed by the actual survivor
and boundary coframes, owns the uncut mixed metric corner. -/
noncomputable def g8MetricSurvivorBoundaryFixedPairData
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
    BasisHilbertSchmidtPairData (G := commonBoundaryCarrier a c) sourceBasis :=
  (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)).boundedPrecomp
      boundaryBasis sourceBasis
      (g8MetricSurvivorCoframe lambda family)
      (g8MetricVisibleBoundaryCoframe lambda family)

theorem g8MetricSurvivorBoundaryFixedPairData_traceProduct_eq
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
    (g8MetricSurvivorBoundaryFixedPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis).traceProduct =
      (g8MetricSurvivorCoframe lambda family).adjoint ∘L
        detectorOperator owner ∘L g8MetricVisibleBoundaryCoframe lambda family := by
  let P := sourceSoninProjection lambda
  let S := g8MetricSurvivorCoframe lambda family
  let B := g8MetricVisibleBoundaryCoframe lambda family
  let J := sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)
  rw [g8MetricSurvivorBoundaryFixedPairData,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis
      (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda),
    ← sourceSoninCommutator_eq_threeBranch]
  have hSP : S.adjoint ∘L P = S.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint
      (sourceSoninProjection_comp_g8MetricSurvivor_eq lambda family)
    simpa only [ContinuousLinearMap.adjoint_comp,
      (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
      ContinuousLinearMap.adjoint_adjoint] using h
  have hPB : P ∘L B = 0 := by
    exact sourceSoninProjection_comp_g8MetricVisibleBoundary_eq_zero lambda family
  apply ContinuousLinearMap.ext
  intro x
  change S.adjoint ((P ∘L detectorOperator owner -
    detectorOperator owner ∘L P) (B x)) =
      S.adjoint (detectorOperator owner (B x))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  have hSPpoint (y : finiteSCarrier) : S.adjoint (P y) = S.adjoint y :=
    DFunLike.congr_fun hSP y
  have hPBpoint : P (B x) = 0 := by
    exact DFunLike.congr_fun hPB x
  rw [hSPpoint, hPBpoint]
  simp

/- The fixed trace transfer and the exact channel readback need additional
heartbeats because they retain the full three-branch pair. -/
set_option maxHeartbeats 6000000 in
-- The full same-owner pair and both cutoff readbacks need this budget.
theorem tendsto_ordinaryTraceAlong_g8MetricSurvivorVisibleBoundary_actualCutoff
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
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family))) atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
          (g8MetricSurvivorCoframe lambda family).adjoint ∘L
            detectorOperator owner ∘L
              g8MetricVisibleBoundaryCoframe lambda family ∘L
                g8SourceCompressedGlobalConvolution lambda owner.sourceTest))) := by
  let cutoff : ℕ → sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedPhysicalCutoff owner lambda
  let limitCutoff : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    g8SourceCompressedGlobalConvolution lambda owner.sourceTest
  let pair := g8MetricSurvivorBoundaryFixedPairData owner lambda family a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis sourceBasis
  have hcutoff_bound : ∀ n, ‖cutoff n‖ ≤
      ‖cc20GlobalLogConvolution owner.sourceTest.involution.test‖ := by
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
  have hC (n : ℕ) :
      (sourceInclusion lambda).adjoint ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left =
      cutoff n := by
    simp [cutoff, g8SourceCompressedPhysicalCutoff, g8SourceCutoffPairData,
      g8CutoffPairData, Source.Dev.C1Stage3ProjectionWindow.kernelSandwichPairData]
  have hchannel (n : ℕ) :
      g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family) =
        (cutoff n).adjoint ∘L pair.traceProduct ∘L cutoff n := by
    rw [g8MetricCutoffChannel]
    rw [hC n]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    rw [g8MetricSurvivorBoundaryFixedPairData_traceProduct_eq owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
      boundaryBasis sourceBasis]
    rfl
  have htraceSequence :
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family))) =
      (fun n => ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich boundaryBasis (cutoff n).adjoint
          (cutoff n)).traceProduct)) := by
    funext n
    rw [hchannel n, pair.boundedSandwich_traceProduct_eq]
  have hlimitEq :
      (pair.boundedSandwich boundaryBasis limitCutoff.adjoint limitCutoff).traceProduct =
        limitCutoff.adjoint ∘L
          (g8MetricSurvivorCoframe lambda family).adjoint ∘L
            detectorOperator owner ∘L
              g8MetricVisibleBoundaryCoframe lambda family ∘L limitCutoff := by
    rw [pair.boundedSandwich_traceProduct_eq,
      g8MetricSurvivorBoundaryFixedPairData_traceProduct_eq owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis sourceBasis]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [htraceSequence]
  simpa only [hlimitEq] using hgeneric

set_option maxHeartbeats 1000000 in
-- The paired mixed-channel limit follows by adjoint symmetry and trace additivity.
/-- The two ordered survivor/boundary channels have a real paired limit on
the same actual cutoff and detector owner. -/
theorem tendsto_ordinaryTraceAlong_g8MetricPairedSurvivorBoundary_actualCutoff
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
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family) +
         g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricSurvivorCoframe lambda family))) atTop
      (𝓝 ((2 * (ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
          (g8MetricSurvivorCoframe lambda family).adjoint ∘L
            detectorOperator owner ∘L
              g8MetricVisibleBoundaryCoframe lambda family ∘L
                g8SourceCompressedGlobalConvolution lambda owner.sourceTest)).re : ℝ) : ℂ)) := by
  let forwardLimit := ordinaryTraceAlong sourceBasis
    ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
      (g8MetricSurvivorCoframe lambda family).adjoint ∘L
        detectorOperator owner ∘L
          g8MetricVisibleBoundaryCoframe lambda family ∘L
            g8SourceCompressedGlobalConvolution lambda owner.sourceTest)
  have hforward :=
    tendsto_ordinaryTraceAlong_g8MetricSurvivorVisibleBoundary_actualCutoff
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis
  have hbackward : Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricSurvivorCoframe lambda family))) atTop
      (𝓝 (star forwardLimit)) := by
    have hseq : (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricSurvivorCoframe lambda family))) =
      (fun n => star (ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricSurvivorCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family)))) := by
      funext n
      have hpair :=
        g8MetricCutoffSurvivorBoundaryChannel_eq_adjoint owner lambda family
          globalBasis sourceBasis n
      have hpair' :
          g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricSurvivorCoframe lambda family) =
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricSurvivorCoframe lambda family)
              (g8MetricVisibleBoundaryCoframe lambda family)).adjoint := by
        have hadj := congrArg ContinuousLinearMap.adjoint hpair
        simpa only [ContinuousLinearMap.adjoint_adjoint] using hadj.symm
      rw [hpair', ordinaryTraceAlong_adjoint]
    rw [hseq]
    simpa only [Complex.star_def, forwardLimit] using
      (Complex.continuous_conj.tendsto _).comp hforward
  have hforwardTraceClass (n : ℕ) :=
    g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
        (g8MetricVisibleBoundaryCoframe lambda family)
  have hbackwardTraceClass (n : ℕ) :=
    g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
        (g8MetricSurvivorCoframe lambda family)
  have htraceSum :
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricSurvivorCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family) +
          g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricSurvivorCoframe lambda family))) =
      (fun n => ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricSurvivorCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family)) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricSurvivorCoframe lambda family))) := by
    funext n
    exact ordinaryTraceAlong_add sourceBasis _ _
      (hforwardTraceClass n) (hbackwardTraceClass n)
  rw [htraceSum]
  convert hforward.add hbackward using 1
  rw [Complex.star_def, Complex.add_conj]

end Dev
end ConnesWeilRH
