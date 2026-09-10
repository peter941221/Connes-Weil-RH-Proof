import ConnesWeilRH.Dev.C1G8P1BoundaryColumnEnergy
import ConnesWeilRH.Dev.C1G8P1MetricChannels
import ConnesWeilRH.Dev.C1G8AdjointShearGram

/-!
# G8 P1 boundary-energy readout

The completed metric history already controls the full survivor/boundary
carrier.  This leaf records the corresponding bound for the literal visible
boundary coframe, with the finite Euler upper factor kept explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1BoundaryEnergyExtension

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSTransportBounds
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSJuliaCoDefect
open CCM25Concrete.CCM24FiniteSJuliaBessel
open CCM25Concrete.CCM24FiniteSGramInverseCalculus
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24SourceProlateTrace
open CC20Concrete.PositiveTrace
open CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open C1G8AdjointShearGram
open C1G8P1MetricChannels
open C1G8P1BoundaryColumnEnergy
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem norm_finiteEulerMetricBoundaryColumn_le_history
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖finiteEulerMetricBoundaryColumn lambda S x‖ ≤
      ‖finiteEulerMetricCoframeHistoryColumn lambda S x‖ := by
  simpa only [finiteEulerMetricCoframeHistoryColumn_apply,
    WithLp.toLp_snd] using
    (WithLp.norm_snd_le (α := sourceSoninCarrier lambda)
      (β := PiLp 2 (fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
          finiteSCarrier)) (p := 2)
      (WithLp.toLp 2
        (juliaSurvivor
            ((suffixEulerFrameSchurSteps lambda S).map
              (fun step => step.toAdjointCoDefectJuliaStep)) x,
          finiteEulerMetricBoundaryColumn lambda S x)))

theorem finiteEulerMetricBoundaryColumn_summable_normSq_of_summable_input
    {ι K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis ι ℂ K)
    (input : K →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    Summable fun i =>
      ‖finiteEulerMetricBoundaryColumn lambda S
        (input (sourceBasis i))‖ ^ 2 := by
  have hhistory :=
    finiteEulerMetricCoframeHistoryColumn_summable_normSq_of_summable_input
      lambda S sourceBasis input hinput
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => ?_)
    hhistory
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_finiteEulerMetricBoundaryColumn_le_history lambda S
      (input (sourceBasis i)))

theorem finiteEulerMetricBoundaryColumn_tsum_normSq_le_of_summable_input
    {ι K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis ι ℂ K)
    (input : K →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    (∑' i, ‖finiteEulerMetricBoundaryColumn lambda S
        (input (sourceBasis i))‖ ^ 2) ≤
      ∑' i, ‖finiteEulerMetricCoframeHistoryColumn lambda S
        (input (sourceBasis i))‖ ^ 2 := by
  have hboundary :=
    finiteEulerMetricBoundaryColumn_summable_normSq_of_summable_input
      lambda S sourceBasis input hinput
  have hhistory :=
    finiteEulerMetricCoframeHistoryColumn_summable_normSq_of_summable_input
      lambda S sourceBasis input hinput
  exact hboundary.tsum_le_tsum
    (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_finiteEulerMetricBoundaryColumn_le_history lambda S
        (input (sourceBasis i))))
    hhistory

theorem finiteEulerMetricBoundaryColumn_tsum_normSq_le_sourceProlateFactor
    {nu rho : Type*}
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖finiteEulerMetricBoundaryColumn lambda S
        (((sourceInclusion lambda)† ∘L
          sourceProlateHilbertSchmidtFactor lambda ∘L
            sourceInclusion lambda) (sourceBasis i))‖ ^ 2) ≤
      ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
        (globalBasis i)‖ ^ 2 := by
  let factor := sourceProlateHilbertSchmidtFactor lambda
  let inclusion := sourceInclusion lambda
  let inclusionAdj := (inclusion)†
  let input : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    inclusionAdj ∘L factor ∘L inclusion
  have hpre : Summable fun i =>
      ‖(factor ∘L inclusion) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp globalBasis globalBasis sourceBasis
      factor inclusion hfactor
  have hinclusionAdj : ‖inclusionAdj‖ ≤ (1 : ℝ) := by
    calc
      ‖inclusionAdj‖ = ‖inclusion‖ := by
        exact ContinuousLinearMap.adjoint.norm_map inclusion
      _ ≤ 1 := Submodule.norm_subtypeL_le _
  have hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2 := by
    apply Summable.of_nonneg_of_le
      (fun i => sq_nonneg _)
      (fun i => ?_)
      (hpre.mul_left (‖inclusionAdj‖ ^ 2))
    simp only [input, ContinuousLinearMap.comp_apply]
    calc
      ‖inclusionAdj ((factor ∘L inclusion) (sourceBasis i))‖ ^ 2 ≤
          (‖inclusionAdj‖ * ‖(factor ∘L inclusion) (sourceBasis i)‖) ^ 2 := by
        gcongr
        exact inclusionAdj.le_opNorm _
      _ = ‖inclusionAdj‖ ^ 2 *
          ‖(factor ∘L inclusion) (sourceBasis i)‖ ^ 2 := by ring
  have hboundary :=
    finiteEulerMetricBoundaryColumn_tsum_normSq_le_of_summable_input
      lambda S sourceBasis input hinput
  have hhistory :=
    finiteEulerMetricCoframeHistoryColumn_tsum_normSq_le_sourceProlateFactor
      lambda S globalBasis sourceBasis hfactor
  simpa only [factor, inclusion, inclusionAdj, input,
    ContinuousLinearMap.comp_apply] using hboundary.trans hhistory

end
end C1G8P1BoundaryEnergyExtension
end Source
end ConnesWeilRH
