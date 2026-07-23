/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistory

/-!
# Completed metric-coframe history

The Schur--polar telescope identifies the raw metric coframe with two finite
channels: a terminal survivor and the rectangular boundary outputs after their
remaining ambient adjoints.  This module packs those *metric* outputs into the
same completed `L2` product shape and proves the exact readback.

This is intentionally not the physical endpoint history.  The existing
physical column records raw boundary daggers, and identifying it with a
source-specific physical readout remains a separate producer premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedMetricCoframeReadout

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSCoframeResponse
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSJuliaBessel
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## List-sum helper -/

theorem list_map_apply_sum
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (maps : List (H →L[ℂ] K)) (x : H) :
    (maps.map (fun f => f x)).sum = maps.sum x := by
  induction maps with
  | nil => rfl
  | cons f fs ih =>
      simp only [List.map_cons, List.sum_cons,
        ContinuousLinearMap.add_apply]
      rw [ih]

/-! ## Metric boundary output column -/

noncomputable def finiteEulerMetricBoundaryColumn
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ]
      PiLp 2 (fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
          finiteSCarrier) :=
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
          finiteSCarrier)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
      (suffixEulerBoundaryOutputMaps lambda S).get
        ⟨i, by
          have hmap : ((suffixEulerFrameSchurSteps lambda S).map
              (fun step => step.toAdjointCoDefectJuliaStep)).length = S.length := by
            simp [suffixEulerFrameSchurSteps_length]
          simpa [suffixEulerBoundaryOutputMaps_length, hmap] using i.isLt⟩)

@[simp]
theorem finiteEulerMetricBoundaryColumn_apply
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (i : Fin ((suffixEulerFrameSchurSteps lambda S).map
      (fun step => step.toAdjointCoDefectJuliaStep)).length) :
    finiteEulerMetricBoundaryColumn lambda S x i =
      (suffixEulerBoundaryOutputMaps lambda S).get
        ⟨i, by
          have hmap : ((suffixEulerFrameSchurSteps lambda S).map
              (fun step => step.toAdjointCoDefectJuliaStep)).length = S.length := by
            simp [suffixEulerFrameSchurSteps_length]
          simpa [suffixEulerBoundaryOutputMaps_length, hmap] using i.isLt⟩ x := by
  rfl

noncomputable def finiteEulerMetricBoundarySum
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    PiLp 2 (fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
      (fun step => step.toAdjointCoDefectJuliaStep)).length =>
        finiteSCarrier) →L[ℂ] finiteSCarrier :=
  ∑ i : Fin ((suffixEulerFrameSchurSteps lambda S).map
      (fun step => step.toAdjointCoDefectJuliaStep)).length,
    PiLp.proj (p := 2)
      (β := fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
          finiteSCarrier) i

@[simp]
theorem finiteEulerMetricBoundarySum_apply
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : PiLp 2 (fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
      (fun step => step.toAdjointCoDefectJuliaStep)).length =>
        finiteSCarrier)) :
    finiteEulerMetricBoundarySum lambda S x =
      ∑ i : Fin ((suffixEulerFrameSchurSteps lambda S).map
          (fun step => step.toAdjointCoDefectJuliaStep)).length, x i := by
  simp [finiteEulerMetricBoundarySum]

theorem finiteEulerMetricBoundarySum_comp_column
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    finiteEulerMetricBoundarySum lambda S
        (finiteEulerMetricBoundaryColumn lambda S x) =
      (suffixEulerBoundaryOutputMaps lambda S).sum x := by
  rw [finiteEulerMetricBoundarySum_apply]
  calc
    (∑ i : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length,
        finiteEulerMetricBoundaryColumn lambda S x i) =
        ∑ i : Fin (suffixEulerBoundaryOutputMaps lambda S).length,
          (suffixEulerBoundaryOutputMaps lambda S).get i x := by
      have hlen : (suffixEulerBoundaryOutputMaps lambda S).length =
          ((suffixEulerFrameSchurSteps lambda S).map
            (fun step => step.toAdjointCoDefectJuliaStep)).length := by
        rw [suffixEulerBoundaryOutputMaps_length]
        simp [suffixEulerFrameSchurSteps_length]
      simpa only [finiteEulerMetricBoundaryColumn_apply, hlen,
        List.get_eq_getElem] using
        (Equiv.sum_comp (finCongr hlen.symm)
          (fun i : Fin (suffixEulerBoundaryOutputMaps lambda S).length =>
            (suffixEulerBoundaryOutputMaps lambda S).get i x))
    _ = (suffixEulerBoundaryOutputMaps lambda S).sum x := by
      calc
        (∑ i : Fin (suffixEulerBoundaryOutputMaps lambda S).length,
            (suffixEulerBoundaryOutputMaps lambda S).get i x) =
            ((suffixEulerBoundaryOutputMaps lambda S).map
              (fun f : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
                f x)).sum := by
          simpa only [List.get_eq_getElem] using
            (Fin.sum_univ_fun_getElem (suffixEulerBoundaryOutputMaps lambda S)
              (fun f : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => f x))
        _ = (suffixEulerBoundaryOutputMaps lambda S).sum x :=
          list_map_apply_sum (suffixEulerBoundaryOutputMaps lambda S) x

/-! ## Completed metric history and exact readback -/

noncomputable def finiteEulerMetricCoframeHistoryColumn
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ]
      completedRectangularBoundaryCarrier
        (suffixEulerFrameSchurSteps lambda S) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      (sourceSoninCarrier lambda)
      (PiLp 2 (fun _ : Fin ((suffixEulerFrameSchurSteps lambda S).map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
          finiteSCarrier))).symm.toContinuousLinearMap ∘L
    (juliaSurvivor
        ((suffixEulerFrameSchurSteps lambda S).map
          (fun step => step.toAdjointCoDefectJuliaStep))).prod
      (finiteEulerMetricBoundaryColumn lambda S)

@[simp]
theorem finiteEulerMetricCoframeHistoryColumn_apply
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    finiteEulerMetricCoframeHistoryColumn lambda S x =
      WithLp.toLp 2
        (juliaSurvivor
            ((suffixEulerFrameSchurSteps lambda S).map
              (fun step => step.toAdjointCoDefectJuliaStep)) x,
          finiteEulerMetricBoundaryColumn lambda S x) := by
  rfl

noncomputable def finiteEulerMetricCoframeHistoryReadout
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    completedRectangularBoundaryCarrier
        (suffixEulerFrameSchurSteps lambda family.visiblePrimes) →L[ℂ]
      finiteSCarrier :=
  (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
    (ContinuousLinearMap.coprod
        (newSuffixFrame lambda [])
        (finiteEulerMetricBoundarySum lambda family.visiblePrimes)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ
        (sourceSoninCarrier lambda)
        (PiLp 2 (fun _ : Fin ((suffixEulerFrameSchurSteps lambda
          family.visiblePrimes).map
            (fun step => step.toAdjointCoDefectJuliaStep)).length =>
          finiteSCarrier))).toContinuousLinearMap

@[simp]
theorem finiteEulerMetricCoframeHistoryReadout_apply
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : completedRectangularBoundaryCarrier
      (suffixEulerFrameSchurSteps lambda family.visiblePrimes)) :
    finiteEulerMetricCoframeHistoryReadout lambda family x =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (newSuffixFrame lambda [] x.fst +
          finiteEulerMetricBoundarySum lambda family.visiblePrimes x.snd) := by
  change (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
      (newSuffixFrame lambda [] (WithLp.fst x) +
        finiteEulerMetricBoundarySum lambda family.visiblePrimes
          (WithLp.snd x)) =
    (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
      (newSuffixFrame lambda [] x.fst +
        finiteEulerMetricBoundarySum lambda family.visiblePrimes x.snd)
  rfl

theorem finiteEulerMetricCoframeHistoryReadout_comp_column_eq
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframeHistoryReadout lambda family ∘L
        finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
        parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
          (by norm_num) =
      finiteEulerMetricCoframe lambda family := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  rw [finiteEulerMetricCoframeHistoryReadout_apply,
    finiteEulerMetricCoframeHistoryColumn_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  have hsurvivor :=
    juliaSurvivor_suffixEulerFrameCoDefectSteps lambda
      family.visiblePrimes
  have hsurvivor' :
      juliaSurvivor
          ((suffixEulerFrameSchurSteps lambda family.visiblePrimes).map
            (fun step => step.toAdjointCoDefectJuliaStep)) =
        (suffixEulerTransitionProduct lambda family.visiblePrimes)† := by
    simpa only [suffixEulerFrameCoDefectSteps] using hsurvivor
  have hsurvivorPoint := congrArg
    (fun operator =>
      operator (parameterizedSoninGramInvSqrt lambda 1
        family.visiblePrimes (by norm_num) x)) hsurvivor'
  have hsurvivorPoint' :
      juliaSurvivor
          ((suffixEulerFrameSchurSteps lambda family.visiblePrimes).map
            (fun step => step.toAdjointCoDefectJuliaStep))
          (parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
            (by norm_num) x) =
        ((suffixEulerTransitionProduct lambda family.visiblePrimes)†)
          (parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
            (by norm_num) x) := by
    simpa only [ContinuousLinearMap.comp_apply] using hsurvivorPoint
  rw [hsurvivorPoint']
  rw [finiteEulerMetricBoundarySum_comp_column]
  rw [finiteEulerMetricCoframe_eq_survivor_add_boundarySum]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [finiteEulerMetricCoframeBoundaryMaps, sum_map_comp_apply]

end CCM24FiniteSCompletedMetricCoframeReadout
end CCM25Concrete
end Source
end ConnesWeilRH
