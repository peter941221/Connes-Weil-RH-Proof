/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3OutputProjectionStrongLimit
import ConnesWeilRH.Dev.C1PositiveTraceCutoffAdapter

/-!
# Strong limit of the physical G8 cutoff factor

The finite G8 factor is the expanding output-window projection composed with
one fixed global convolution.  This file identifies that exact owner and
proves strong convergence both before and after compression to the source
Sonin carrier.  Strong convergence is only an operator-level compatibility
result; it does not imply convergence of the associated traces.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.Dev.C1PositiveTraceCutoffAdapter
open Source.Dev.C1PositiveTraceWindowProducer
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open scoped Topology

noncomputable local instance physicalSourceSoninCarrierCompleteSpace
    (lambda : Source.CC20Concrete.CCM24SoninScale) :
    CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private noncomputable def physicalCutoffTail
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : cc20GlobalLogCrossingL2) (n : ℕ) : ℝ → ENNReal :=
  (Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n))ᶜ.indicator
    (fun x => ‖(u : ℝ → ℂ) x‖ₑ ^ (2 : ℝ))

private theorem tendsto_physicalCutoffTail_lintegral
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : cc20GlobalLogCrossingL2) :
    Tendsto (fun n => ∫⁻ x, physicalCutoffTail g u n x ∂(volume : Measure ℝ))
      atTop (𝓝 0) := by
  have hmeas (n : ℕ) :
      AEMeasurable (physicalCutoffTail g u n) (volume : Measure ℝ) := by
    exact ((Lp.memLp u).1.enorm.pow_const (2 : ℝ)).indicator
      (measurableSet_Icc.compl)
  have htotal_lt_top :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := (volume : Measure ℝ)) (p := (2 : ENNReal))
      (f := (u : ℝ → ℂ)) two_ne_zero ENNReal.ofNat_ne_top
      (Lp.eLpNorm_lt_top u)
  have hzero_le_total :
      (∫⁻ x, physicalCutoffTail g u 0 x ∂(volume : Measure ℝ)) ≤
        (∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) := by
    apply lintegral_mono
    intro x
    simp only [physicalCutoffTail, Set.indicator_apply]
    split_ifs <;> simp
  have hzero_lt_top := hzero_le_total.trans_lt htotal_lt_top
  have hzero_ne_top := hzero_lt_top.ne
  have hradius_mono : Monotone (cutoffRadius g) := by
    simpa only [cutoffUpper] using cutoffUpper_monotone g
  have hanti : ∀ x, Antitone (fun n => physicalCutoffTail g u n x) := by
    intro x m n hmn
    by_cases hm : x ∈ Set.Icc (-(cutoffRadius g m)) (cutoffRadius g m)
    · have hn : x ∈ Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n) := by
        have hmnR := hradius_mono hmn
        exact Set.Icc_subset_Icc (by linarith) hmnR hm
      simp [physicalCutoffTail, hm, hn]
    · by_cases hn : x ∈ Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n)
      · simp [physicalCutoffTail, hm, hn]
      · simp [physicalCutoffTail, hm, hn]
  have hradius_ge_nat (n : ℕ) : (n : ℝ) ≤ cutoffRadius g n := by
    dsimp [cutoffRadius]
    have hs := Source.C1SameOwnerWeil.supportRadius_nonnegative g
    linarith
  have hinterval_eventually (x : ℝ) :
      ∀ᶠ n : ℕ in atTop,
        x ∈ Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hn.eventually (eventually_ge_atTop |x|)] with n hnx
    have hxradius : |x| ≤ cutoffRadius g n := hnx.trans (hradius_ge_nat n)
    constructor
    · exact (neg_le_neg hxradius).trans (neg_abs_le x)
    · exact (le_abs_self x).trans hxradius
  have hpoint (x : ℝ) :
      Tendsto (fun n => physicalCutoffTail g u n x) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hinterval_eventually x] with n hn
    simp [physicalCutoffTail, hn]
  have hlintegral := lintegral_tendsto_of_tendsto_of_antitone
    hmeas (ae_of_all _ hanti) hzero_ne_top (ae_of_all _ hpoint)
  simpa [physicalCutoffTail] using hlintegral

private theorem tendsto_physicalCutoffTail_eLpNorm
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ => eLpNorm
        ((Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n))ᶜ.indicator
          (fun x => (u : ℝ → ℂ) x))
        (2 : ENNReal) (volume : Measure ℝ))
      atTop (𝓝 0) := by
  have hlin := tendsto_physicalCutoffTail_lintegral g u
  have hpow : Tendsto
      (fun n : ℕ =>
        (∫⁻ x, physicalCutoffTail g u n x ∂(volume : Measure ℝ)) ^
          (1 / 2 : ℝ))
      atTop (𝓝 ((0 : ENNReal) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hlin
  have hnorm (n : ℕ) :
      eLpNorm
          ((Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n))ᶜ.indicator
            (fun x => (u : ℝ → ℂ) x))
          (2 : ENNReal) (volume : Measure ℝ) =
        (∫⁻ x, physicalCutoffTail g u n x ∂(volume : Measure ℝ)) ^
          (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    congr 1
    apply lintegral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n) <;>
        simp [physicalCutoffTail, hx]
  simpa [hnorm] using hpow

/-- The actual symmetric physical output windows converge strongly on the
whole-line carrier. -/
theorem tendsto_physicalCutoffProjection_apply
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ =>
        kernelIntervalProjection (-(cutoffUpper g n)) (-(cutoffLower g n)) 0 u)
      atTop (𝓝 u) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have herror (n : ℕ) :
      eLpNorm
          ((kernelIntervalProjection (-(cutoffUpper g n))
              (-(cutoffLower g n)) 0 u : ℝ → ℂ) - (u : ℝ → ℂ))
          (2 : ENNReal) (volume : Measure ℝ) =
        eLpNorm
          ((Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n))ᶜ.indicator
            (fun x => (u : ℝ → ℂ) x))
          (2 : ENNReal) (volume : Measure ℝ) := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [kernelIntervalProjection_coeFn
      (-(cutoffUpper g n)) (-(cutoffLower g n)) 0 u] with x hx
    simp only [Pi.sub_apply]
    have hx' :
        (kernelIntervalProjection (-(cutoffUpper g n))
            (-(cutoffLower g n)) 0 u : ℝ → ℂ) x =
          (Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n)).indicator
            (fun t => (u : ℝ → ℂ) t) x := by
      simpa [cutoffLower, cutoffUpper, sub_zero, add_zero] using hx
    rw [hx']
    by_cases hmem : x ∈ Set.Icc (-(cutoffRadius g n)) (cutoffRadius g n) <;>
      simp [Set.indicator, hmem]
  have herror_tendsto : Tendsto
      (fun n : ℕ => eLpNorm
        ((kernelIntervalProjection (-(cutoffUpper g n))
            (-(cutoffLower g n)) 0 u : ℝ → ℂ) - (u : ℝ → ℂ))
        (2 : ENNReal) (volume : Measure ℝ)) atTop (𝓝 0) := by
    simpa only [herror] using tendsto_physicalCutoffTail_eLpNorm g u
  simpa [Lp.toLp_coeFn] using
    (Lp.tendsto_Lp_of_tendsto_eLpNorm
      (u : ℝ → ℂ) (Lp.memLp u) herror_tendsto)

/-- The finite-window positive factor is exactly the actual output projection
followed by the fixed global root convolution. -/
theorem fullBoundaryPositiveOperator_cutoff_eq_projection_comp_globalConvolution
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (n : ℕ) :
    fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n) =
      kernelIntervalProjection (-(cutoffUpper g n)) (-(cutoffLower g n)) 0 ∘L
        cc20GlobalLogConvolution g.involution.test := by
  have hsupp := support_subset_cutoffWindow g n
  have hroot := fullBoundaryRootFactor_eq_globalConvolution g
    (cutoffLower g n) (cutoffUpper g n) hsupp
  unfold fullBoundaryPositiveOperator fullBoundaryOutputZeroExtension
  rw [hroot]
  unfold kernelIntervalProjection
  simp only [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- The actual physical G8 factor converges strongly to global convolution;
this is still only pointwise operator convergence, not Hilbert--Schmidt or
trace convergence. -/
theorem tendsto_fullBoundaryPositiveOperator_cutoff_apply
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ =>
        fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n) u)
      atTop (𝓝 (cc20GlobalLogConvolution g.involution.test u)) := by
  have h := tendsto_physicalCutoffProjection_apply g
    (cc20GlobalLogConvolution g.involution.test u)
  convert h using 1
  · funext n
    rw [fullBoundaryPositiveOperator_cutoff_eq_projection_comp_globalConvolution]
    rfl

/-- The adjoints of the physical G8 factors also converge strongly, by
self-adjointness of the expanding output projections. -/
theorem tendsto_fullBoundaryPositiveOperator_adjoint_cutoff_apply
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ =>
        (fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n)).adjoint u)
      atTop (𝓝 ((cc20GlobalLogConvolution g.involution.test).adjoint u)) := by
  have hproj := tendsto_physicalCutoffProjection_apply g u
  have hmap :=
    ((cc20GlobalLogConvolution g.involution.test).adjoint.continuous.tendsto u).comp hproj
  convert hmap using 1
  · funext n
    have hfactor := fullBoundaryPositiveOperator_cutoff_eq_projection_comp_globalConvolution
      g n
    rw [hfactor, ContinuousLinearMap.adjoint_comp,
      (Source.CC20Concrete.CompactConvolutionSupport.kernelIntervalProjection_isSelfAdjoint
        (-(cutoffUpper g n)) (-(cutoffLower g n))).adjoint_eq]
    rfl

/-- Strong convergence survives compression by the actual source Sonin
inclusion on both sides of the physical factor. -/
theorem tendsto_sourceCompressedPhysicalCutoff_apply
    (lambda : Source.CC20Concrete.CCM24SoninScale)
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : sourceSoninCarrier lambda) :
    Tendsto
      (fun n : ℕ => (sourceInclusion lambda).adjoint
        (fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n)
          (sourceInclusion lambda u)))
      atTop
      (𝓝 ((sourceInclusion lambda).adjoint
        (cc20GlobalLogConvolution g.involution.test (sourceInclusion lambda u)))) := by
  have h := tendsto_fullBoundaryPositiveOperator_cutoff_apply g
    (sourceInclusion lambda u)
  exact ((sourceInclusion lambda).adjoint.continuous.tendsto _).comp h

/-- The adjoint source compression has the matching strong limit. -/
theorem tendsto_sourceCompressedPhysicalCutoff_adjoint_apply
    (lambda : Source.CC20Concrete.CCM24SoninScale)
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : sourceSoninCarrier lambda) :
    Tendsto
      (fun n : ℕ =>
        ((sourceInclusion lambda).adjoint ∘L
          fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n) ∘L
            sourceInclusion lambda).adjoint u)
      atTop
      (𝓝 (((sourceInclusion lambda).adjoint ∘L
        cc20GlobalLogConvolution g.involution.test ∘L
          sourceInclusion lambda).adjoint u)) := by
  have h := tendsto_fullBoundaryPositiveOperator_adjoint_cutoff_apply g
    (sourceInclusion lambda u)
  have hmap :=
    ((sourceInclusion lambda).adjoint.continuous.tendsto _).comp h
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] using hmap

end Dev
end ConnesWeilRH
