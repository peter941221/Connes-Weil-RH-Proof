import ConnesWeilRH.Dev.C1G8P1CanonicalRadialBoundaryBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout

/-!
# G8 P1 metric-boundary column energy

The metric boundary output list carries the same square-energy budget as the
underlying Julia co-defect cascade.  This is an unconditional quantitative
bound on the literal finite-Euler boundary column; it does not identify that
column with the radial crossing channel or with a finite-prime trace.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1BoundaryColumnEnergy

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSJuliaCoDefect
open CCM25Concrete.CCM24FiniteSJuliaBessel
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open CCM25Concrete.CCM24SourceProlateTrace
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem norm_suffixEulerAmbientProduct_adjoint_le_one
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerAmbientProduct S)†‖ ≤ 1 := by
  induction S with
  | nil =>
      simpa only [suffixEulerAmbientProduct, ContinuousLinearMap.adjoint_id] using
        (ContinuousLinearMap.norm_id_le :
          ‖(ContinuousLinearMap.id ℂ finiteSCarrier)‖ ≤ 1)
  | cons p S ih =>
      rw [show suffixEulerAmbientProduct (p :: S) =
          normalizedPrimeEulerFrameTransport p ∘L
            suffixEulerAmbientProduct S by rfl]
      rw [ContinuousLinearMap.adjoint_comp]
      calc
        ‖(suffixEulerAmbientProduct S)† ∘L
            (normalizedPrimeEulerFrameTransport p)†‖ ≤
            ‖(suffixEulerAmbientProduct S)†‖ *
              ‖(normalizedPrimeEulerFrameTransport p)†‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := mul_le_mul ih
          (by simpa only [ContinuousLinearMap.adjoint.norm_map] using
            normalizedPrimeEulerFrameTransport_norm_le_one p)
          (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul 1

theorem suffixEulerBoundaryOutputMaps_normSq_sum_le_juliaDefectEnergy
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ((suffixEulerBoundaryOutputMaps lambda S).map
      (fun f => ‖f x‖ ^ 2)).sum ≤
      juliaDefectEnergy
        ((suffixEulerFrameSchurSteps lambda S).map
          (fun step => step.toAdjointCoDefectJuliaStep)) x := by
  induction S generalizing x with
  | nil =>
      simp [suffixEulerBoundaryOutputMaps, suffixEulerFrameSchurSteps,
        juliaDefectEnergy]
  | cons p S ih =>
      let step := suffixEulerFrameSchurStep lambda p S
      have hlocal :
          ‖((suffixEulerAmbientProduct S)† ∘L step.boundaryDagger) x‖ ^ 2 ≤
            ‖step.leftCoDefect x‖ ^ 2 := by
        have hnorm :
            ‖((suffixEulerAmbientProduct S)† ∘L step.boundaryDagger) x‖ ≤
              ‖step.leftCoDefect x‖ := by
          calc
            ‖((suffixEulerAmbientProduct S)† ∘L step.boundaryDagger) x‖ ≤
                ‖(suffixEulerAmbientProduct S)†‖ *
                  ‖step.boundaryDagger x‖ := by
              exact ((suffixEulerAmbientProduct S)†).le_opNorm _
            _ ≤ ‖step.boundaryDagger x‖ := by
              calc
                ‖(suffixEulerAmbientProduct S)†‖ * ‖step.boundaryDagger x‖ ≤
                    1 * ‖step.boundaryDagger x‖ :=
                  mul_le_mul_of_nonneg_right
                    (norm_suffixEulerAmbientProduct_adjoint_le_one S)
                    (norm_nonneg _)
                _ = ‖step.boundaryDagger x‖ := one_mul _
            _ ≤ ‖step.leftCoDefect x‖ := by
              rw [RectangularSchurCoDefectStepData.boundaryDagger,
                step.boundaryDagger_eq_adjoint]
              exact step.boundaryDagger_norm_le_leftCoDefect x
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
      have htail := ih
        ((ContinuousLinearMap.adjoint
          (suffixEulerFrameTransition lambda p S)) x)
      simpa only [suffixEulerBoundaryOutputMaps, suffixEulerFrameSchurSteps,
        List.map_cons, List.map_map, List.sum_cons,
        ContinuousLinearMap.comp_apply, juliaDefectEnergy,
        RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_defect,
        RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_transfer,
        step] using add_le_add hlocal htail

theorem finiteEulerMetricBoundaryColumn_normSq_le_juliaDefectEnergy
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖finiteEulerMetricBoundaryColumn lambda S x‖ ^ 2 ≤
      juliaDefectEnergy
        ((suffixEulerFrameSchurSteps lambda S).map
          (fun step => step.toAdjointCoDefectJuliaStep)) x := by
  change ‖WithLp.toLp 2
      (fun i : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
        finiteEulerMetricBoundaryColumn lambda S x i)‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2]
  have hlen : (suffixEulerBoundaryOutputMaps lambda S).length =
      ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length := by
    rw [suffixEulerBoundaryOutputMaps_length]
    simp [suffixEulerFrameSchurSteps_length]
  calc
    ∑ i : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length,
        ‖finiteEulerMetricBoundaryColumn lambda S x i‖ ^ 2 =
      ((suffixEulerBoundaryOutputMaps lambda S).map
        (fun f => ‖f x‖ ^ 2)).sum := by
      calc
        ∑ i : Fin ((suffixEulerFrameSchurSteps lambda S).map
            (fun step => step.toAdjointCoDefectJuliaStep)).length,
            ‖finiteEulerMetricBoundaryColumn lambda S x i‖ ^ 2 =
          ∑ i : Fin (suffixEulerBoundaryOutputMaps lambda S).length,
            ‖(suffixEulerBoundaryOutputMaps lambda S).get i x‖ ^ 2 := by
          simpa only [finiteEulerMetricBoundaryColumn_apply, hlen,
            List.get_eq_getElem] using
            (Equiv.sum_comp (finCongr hlen.symm)
              (fun i : Fin (suffixEulerBoundaryOutputMaps lambda S).length =>
                ‖(suffixEulerBoundaryOutputMaps lambda S).get i x‖ ^ 2))
        _ = ((suffixEulerBoundaryOutputMaps lambda S).map
            (fun f => ‖f x‖ ^ 2)).sum := by
          simpa only [List.get_eq_getElem] using
            (Fin.sum_univ_fun_getElem (suffixEulerBoundaryOutputMaps lambda S)
              (fun f : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
                ‖f x‖ ^ 2))
    _ ≤ juliaDefectEnergy
        ((suffixEulerFrameSchurSteps lambda S).map
          (fun step => step.toAdjointCoDefectJuliaStep)) x :=
      suffixEulerBoundaryOutputMaps_normSq_sum_le_juliaDefectEnergy
        lambda S x

theorem finiteEulerMetricBoundaryColumn_normSq_le_normSq
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖finiteEulerMetricBoundaryColumn lambda S x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  exact (finiteEulerMetricBoundaryColumn_normSq_le_juliaDefectEnergy
    lambda S x).trans (juliaDefectEnergy_le_normSq
      ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)) x)

theorem finiteEulerMetricCoframeHistoryColumn_normSq_le_normSq
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖finiteEulerMetricCoframeHistoryColumn lambda S x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let defectSteps :=
    (suffixEulerFrameSchurSteps lambda S).map
      (fun step => step.toAdjointCoDefectJuliaStep)
  rw [finiteEulerMetricCoframeHistoryColumn_apply]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  have hboundary :
      ‖finiteEulerMetricBoundaryColumn lambda S x‖ ^ 2 ≤
        juliaDefectEnergy defectSteps x := by
    simpa only [defectSteps] using
      finiteEulerMetricBoundaryColumn_normSq_le_juliaDefectEnergy lambda S x
  calc
    ‖juliaSurvivor defectSteps x‖ ^ 2 +
          ‖finiteEulerMetricBoundaryColumn lambda S x‖ ^ 2 ≤
        ‖juliaSurvivor defectSteps x‖ ^ 2 +
          juliaDefectEnergy defectSteps x :=
      add_le_add_right hboundary _
    _ = juliaDefectEnergy defectSteps x +
          ‖juliaSurvivor defectSteps x‖ ^ 2 := add_comm _ _
    _ = ‖x‖ ^ 2 := juliaDefectEnergy_add_survivor_normSq defectSteps x

theorem finiteEulerMetricCoframeHistoryColumn_summable_normSq_of_summable_input
    {iota K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis iota ℂ K)
    (input : K →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    Summable fun i =>
      ‖finiteEulerMetricCoframeHistoryColumn lambda S
          (input (sourceBasis i))‖ ^ 2 := by
  exact Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => finiteEulerMetricCoframeHistoryColumn_normSq_le_normSq
      lambda S (input (sourceBasis i))) hinput

theorem finiteEulerMetricCoframeHistoryColumn_tsum_normSq_le_of_summable_input
    {iota K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis iota ℂ K)
    (input : K →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    (∑' i, ‖finiteEulerMetricCoframeHistoryColumn lambda S
        (input (sourceBasis i))‖ ^ 2) ≤
      ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
  have hcolumn :=
    finiteEulerMetricCoframeHistoryColumn_summable_normSq_of_summable_input
      lambda S sourceBasis input hinput
  exact hcolumn.tsum_le_tsum
    (fun i => finiteEulerMetricCoframeHistoryColumn_normSq_le_normSq
      lambda S (input (sourceBasis i))) hinput

/-! The first concrete same-owner consumer: the metric boundary history can
be fed the genuine source-prolate Hilbert--Schmidt factor through the source
inclusion, with no carrier-changing adapter.  The estimate is the exact
finite-Euler/JULIA energy budget needed by the later cutoff-trace consumer. -/
theorem finiteEulerMetricCoframeHistoryColumn_tsum_normSq_le_sourceProlateFactor
    {nu rho : Type*}
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖finiteEulerMetricCoframeHistoryColumn lambda S
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
  have hhistory :=
    finiteEulerMetricCoframeHistoryColumn_tsum_normSq_le_of_summable_input
      lambda S sourceBasis input hinput
  have hpreAdj : (∑' i, ‖input (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖(factor ∘L inclusion) (sourceBasis i)‖ ^ 2 := by
    apply hinput.tsum_le_tsum
    · intro i
      simp only [input, ContinuousLinearMap.comp_apply]
      have hnorm : ‖inclusionAdj
            ((factor ∘L inclusion) (sourceBasis i))‖ ≤
          ‖(factor ∘L inclusion) (sourceBasis i)‖ := by
        calc
          ‖inclusionAdj ((factor ∘L inclusion) (sourceBasis i))‖ ≤
              ‖inclusionAdj‖ *
                ‖(factor ∘L inclusion) (sourceBasis i)‖ :=
            inclusionAdj.le_opNorm _
          _ ≤ 1 * ‖(factor ∘L inclusion) (sourceBasis i)‖ := by
            exact mul_le_mul_of_nonneg_right hinclusionAdj (norm_nonneg _)
          _ = ‖(factor ∘L inclusion) (sourceBasis i)‖ := one_mul _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
    · exact hpre
  have hpreT := tsum_normSq_precomp_le globalBasis globalBasis sourceBasis
    factor inclusion hfactor
  have hinclusion : ‖inclusion‖ ^ 2 ≤ (1 : ℝ) := by
    have h : ‖inclusion‖ ≤ (1 : ℝ) := Submodule.norm_subtypeL_le _
    simpa using ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr h)
  have hfactorSum : 0 ≤ (∑' i, ‖factor (globalBasis i)‖ ^ 2) :=
    tsum_nonneg (fun i => sq_nonneg _)
  have hpreBound : (∑' i, ‖(factor ∘L inclusion)
      (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖factor (globalBasis i)‖ ^ 2 := by
    calc
      (∑' i, ‖(factor ∘L inclusion) (sourceBasis i)‖ ^ 2) ≤
          ‖inclusion‖ ^ 2 * (∑' i, ‖factor (globalBasis i)‖ ^ 2) := hpreT
      _ ≤ 1 * (∑' i, ‖factor (globalBasis i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hinclusion hfactorSum
      _ = ∑' i, ‖factor (globalBasis i)‖ ^ 2 := one_mul _
  have hinputBound : (∑' i, ‖input (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖factor (globalBasis i)‖ ^ 2 := hpreAdj.trans hpreBound
  exact hhistory.trans hinputBound

end
end C1G8P1BoundaryColumnEnergy
end Source
end ConnesWeilRH
