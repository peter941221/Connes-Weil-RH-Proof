/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.WindowContainment
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Common logarithmic Haar carrier

The multiplicative Haar measure `d rho / rho` becomes Lebesgue measure after
the coordinate change `rho = exp t`.  This module records the common global
`L2` carrier and the finite logarithmic-window cutoffs.  It does not yet claim
that the parameterized subtype `L2` spaces have been transported into this
carrier; that requires the explicit change-of-variables theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped ComplexConjugate ContDiff ENNReal

noncomputable abbrev cc20GlobalLogL2 := Lp ℂ 2 (volume : Measure ℝ)

noncomputable def cc20LogWindow (lambda : ℝ) : Set ℝ :=
  Set.Icc (-Real.log lambda) (Real.log lambda)

theorem measurableSet_cc20LogWindow (lambda : ℝ) :
    MeasurableSet (cc20LogWindow lambda) := by
  exact measurableSet_Icc

theorem cc20LogWindow_log_pos
    (lambda : ℝ) (hlambda : 1 < lambda) :
    0 < Real.log lambda :=
  Real.log_pos hlambda

theorem cc20LogWindow_volume_ne_zero
    (lambda : ℝ) (hlambda : 1 < lambda) :
    volume (cc20LogWindow lambda) ≠ 0 := by
  rw [cc20LogWindow, Real.volume_Icc]
  have hlog : 0 < Real.log lambda := cc20LogWindow_log_pos lambda hlambda
  have : 0 < Real.log lambda - -Real.log lambda := by linarith
  simpa [ENNReal.ofReal_eq_zero, this.ne']

theorem cc20LogWindow_volume_ne_top
    (lambda : ℝ) (_hlambda : 1 < lambda) :
    volume (cc20LogWindow lambda) ≠ ⊤ := by
  rw [cc20LogWindow, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

noncomputable instance cc20LogWindowRestrictIsFiniteMeasure
    (lambda : ℝ) :
    IsFiniteMeasure (volume.restrict (cc20LogWindow lambda)) := by
  rw [cc20LogWindow]
  infer_instance

noncomputable def cc20LogWindowIndicator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  indicatorConstLp ∞
    (measurableSet_cc20LogWindow lambda)
    (cc20LogWindow_volume_ne_top lambda hlambda)
    (1 : ℂ)

theorem norm_cc20LogWindowIndicator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ‖cc20LogWindowIndicator lambda hlambda‖ = 1 := by
  unfold cc20LogWindowIndicator
  rw [norm_indicatorConstLp_top (cc20LogWindow_volume_ne_zero lambda hlambda)]
  exact norm_one

noncomputable def cc20LogWindowProjectionLinearMap
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogL2 →ₗ[ℂ] cc20GlobalLogL2 where
  toFun u := cc20LogWindowIndicator lambda hlambda • u
  map_add' u v := by
    exact Lp.add_smul _ _ _
  map_smul' c u := by
    exact (Lp.smul_comm (𝕜' := ℂ) (𝕜 := ℂ) (E := ℂ)
      (p := ∞) (q := 2) (r := 2) c _ u).symm

noncomputable def cc20LogWindowProjection
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogL2 →L[ℂ] cc20GlobalLogL2 :=
  LinearMap.mkContinuous
    (cc20LogWindowProjectionLinearMap lambda hlambda)
    1
    (fun u => by
      calc
        ‖cc20LogWindowProjectionLinearMap lambda hlambda u‖ ≤
            ‖cc20LogWindowIndicator lambda hlambda‖ * ‖u‖ :=
          Lp.norm_smul_le _ _
        _ = 1 * ‖u‖ := by rw [norm_cc20LogWindowIndicator])

noncomputable def cc20LogWindowRestrictIndicatorLinearMap
    (lambda : ℝ) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →ₗ[ℂ]
      cc20GlobalLogL2 where
  toFun v :=
    ((memLp_indicator_iff_restrict
        (measurableSet_cc20LogWindow lambda)).2
        (Lp.memLp v)).toLp
      ((cc20LogWindow lambda).indicator v)
  map_add' v w := by
    let hv :=
      (memLp_indicator_iff_restrict
        (measurableSet_cc20LogWindow lambda)).2 (Lp.memLp v)
    let hw :=
      (memLp_indicator_iff_restrict
        (measurableSet_cc20LogWindow lambda)).2 (Lp.memLp w)
    let hvw :=
      (memLp_indicator_iff_restrict
        (measurableSet_cc20LogWindow lambda)).2 (Lp.memLp (v + w))
    apply MemLp.toLp_congr hvw (hv.add hw)
    refine ae_of_ae_restrict_of_ae_restrict_compl
      (cc20LogWindow lambda) ?_ ?_
    · filter_upwards
        [Lp.coeFn_add v w,
          ae_restrict_mem (measurableSet_cc20LogWindow lambda)] with t hsum ht
      simp only [Set.indicator_of_mem ht, Pi.add_apply]
      simpa only [Pi.add_apply] using hsum
    · filter_upwards
        [ae_restrict_mem
          (measurableSet_cc20LogWindow lambda).compl] with t ht
      have hnot : t ∉ cc20LogWindow lambda := ht
      simp [Set.indicator, hnot]
  map_smul' c v := by
    let hv :=
      (memLp_indicator_iff_restrict
        (measurableSet_cc20LogWindow lambda)).2 (Lp.memLp v)
    let hcv :=
      (memLp_indicator_iff_restrict
        (measurableSet_cc20LogWindow lambda)).2 (Lp.memLp (c • v))
    apply MemLp.toLp_congr hcv (hv.const_smul c)
    refine ae_of_ae_restrict_of_ae_restrict_compl
      (cc20LogWindow lambda) ?_ ?_
    · filter_upwards
        [Lp.coeFn_smul c v,
          ae_restrict_mem (measurableSet_cc20LogWindow lambda)] with t hsmul ht
      simp only [Set.indicator_of_mem ht, Pi.smul_apply]
      simpa only [Pi.smul_apply] using hsmul
    · filter_upwards
        [ae_restrict_mem
          (measurableSet_cc20LogWindow lambda).compl] with t ht
      have hnot : t ∉ cc20LogWindow lambda := ht
      simp [Set.indicator, hnot]

theorem norm_cc20LogWindowRestrictIndicatorLinearMap_le
    (lambda : ℝ) (v : Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) :
    ‖cc20LogWindowRestrictIndicatorLinearMap lambda v‖ ≤ ‖v‖ := by
  change ‖((memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (Lp.memLp v)).toLp
      ((cc20LogWindow lambda).indicator v)‖ ≤ ‖v‖
  rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (measurableSet_cc20LogWindow lambda)]
  exact le_rfl

noncomputable def cc20LogWindowRestrictIndicatorCLM
    (lambda : ℝ) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →L[ℂ]
      cc20GlobalLogL2 :=
  LinearMap.mkContinuous
    (cc20LogWindowRestrictIndicatorLinearMap lambda)
    1
    (fun v => by
      rw [one_mul]
      exact norm_cc20LogWindowRestrictIndicatorLinearMap_le lambda v)

theorem cc20LogWindowProjection_coeFn
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2) :
    (cc20LogWindowProjection lambda hlambda u : ℝ → ℂ) =ᵐ[volume]
      (cc20LogWindow lambda).indicator fun t => u t := by
  change
    (cc20LogWindowIndicator lambda hlambda • u : cc20GlobalLogL2) =ᵐ[volume]
      (cc20LogWindow lambda).indicator fun t => u t
  have hindicator :
      (cc20LogWindowIndicator lambda hlambda : ℝ → ℂ) =ᵐ[volume]
        (cc20LogWindow lambda).indicator fun _t => (1 : ℂ) := by
    exact indicatorConstLp_coeFn
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) (cc20LogWindowIndicator lambda hlambda) u,
      hindicator] with t hmul hind
  rw [hmul, Pi.smul_apply', hind]
  by_cases ht : t ∈ cc20LogWindow lambda <;> simp [Set.indicator, ht]

theorem cc20LogWindowProjection_idempotent
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2) :
    cc20LogWindowProjection lambda hlambda
        (cc20LogWindowProjection lambda hlambda u) =
      cc20LogWindowProjection lambda hlambda u := by
  rw [Lp.ext_iff]
  filter_upwards
    [cc20LogWindowProjection_coeFn lambda hlambda
      (cc20LogWindowProjection lambda hlambda u),
      cc20LogWindowProjection_coeFn lambda hlambda u] with t hleft hright
  rw [hleft, hright]
  by_cases ht : t ∈ cc20LogWindow lambda
  · simpa [Set.indicator, ht] using hright
  · simp [Set.indicator, ht]

theorem cc20LogWindow_subset_of_le
    (lambda mu : ℝ) (hlambda : 1 < lambda) (hmu : 1 < mu)
    (hle : lambda ≤ mu) :
    cc20LogWindow lambda ⊆ cc20LogWindow mu := by
  intro t ht
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hmu_pos : 0 < mu := lt_trans (by norm_num) hmu
  have hlog : Real.log lambda ≤ Real.log mu :=
    Real.log_le_log hlambda_pos hle
  exact ⟨by linarith [ht.1, hlog], by linarith [ht.2, hlog]⟩

theorem cc20LogWindowProjection_comp_of_le
    (lambda mu : ℝ) (hlambda : 1 < lambda) (hmu : 1 < mu)
    (hle : lambda ≤ mu) (u : cc20GlobalLogL2) :
    cc20LogWindowProjection lambda hlambda
        (cc20LogWindowProjection mu hmu u) =
      cc20LogWindowProjection lambda hlambda u := by
  have hsubset : cc20LogWindow lambda ⊆ cc20LogWindow mu :=
    cc20LogWindow_subset_of_le lambda mu hlambda hmu hle
  rw [Lp.ext_iff]
  filter_upwards
    [cc20LogWindowProjection_coeFn lambda hlambda
      (cc20LogWindowProjection mu hmu u),
      cc20LogWindowProjection_coeFn mu hmu u,
      cc20LogWindowProjection_coeFn lambda hlambda u] with t hleft hmid hright
  by_cases ht : t ∈ cc20LogWindow lambda
  · rw [hleft, hright]
    simp only [Set.indicator_of_mem ht]
    rw [hmid]
    simp [Set.indicator, hsubset ht]
  · rw [hleft, hright]
    simp [Set.indicator, ht]

noncomputable def cc20LogPullback
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ℝ → ℂ :=
  fun t => normalizedCC20ConcreteTestAlgebra.legacy.encode p.test (Real.exp t)

theorem continuous_cc20LogPullback
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    Continuous (cc20LogPullback p) := by
  exact
    (SchwartzMap.continuous
      (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test)).comp
        Real.continuous_exp

theorem contDiff_cc20LogPullback
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ContDiff ℝ ∞ (cc20LogPullback p) := by
  exact
    ((normalizedCC20ConcreteTestAlgebra.legacy.encode p.test).smooth ⊤).comp
      Real.contDiff_exp

theorem cc20LogPullback_support_subset
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    Function.support (cc20LogPullback p) ⊆
      Set.Icc (Real.log p.lower) (Real.log p.upper) := by
  intro t ht
  have hvalue :
      normalizedCC20ConcreteTestAlgebra.legacy.encode p.test (Real.exp t) ≠ 0 := ht
  have hsource : Real.exp t ∈ Set.Icc p.lower p.upper := by
    apply p.support_subset
    simpa [Function.mem_support] using hvalue
  constructor
  · simpa using
      (Real.log_le_log_iff p.lower_pos (Real.exp_pos t)).2 hsource.1
  · have hupper_pos : 0 < p.upper :=
      lt_of_lt_of_le (Real.exp_pos t) hsource.2
    simpa using
      (Real.log_le_log_iff (Real.exp_pos t) hupper_pos).2 hsource.2

theorem hasCompactSupport_cc20LogPullback
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    HasCompactSupport (cc20LogPullback p) := by
  apply HasCompactSupport.intro
    (K := Set.Icc (Real.log p.lower) (Real.log p.upper)) isCompact_Icc
  intro t ht
  by_contra hzero
  exact ht (cc20LogPullback_support_subset p hzero)

noncomputable def cc20LogPullbackSchwartz
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_cc20LogPullback p).toSchwartzMap
    (contDiff_cc20LogPullback p)

theorem cc20LogPullbackSchwartz_coe
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    (cc20LogPullbackSchwartz p : ℝ → ℂ) = cc20LogPullback p := by
  rfl

theorem cc20LogPullbackSchwartz_support_subset
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    Function.support (cc20LogPullbackSchwartz p : ℝ → ℂ) ⊆
      Set.Icc (Real.log p.lower) (Real.log p.upper) := by
  simpa only [cc20LogPullbackSchwartz_coe] using
    cc20LogPullback_support_subset p

theorem cc20LogPullback_memLp
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    MemLp (cc20LogPullback p) 2 volume := by
  exact (continuous_cc20LogPullback p).memLp_of_hasCompactSupport
    (hasCompactSupport_cc20LogPullback p)

noncomputable def cc20LogPullbackLp
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    cc20GlobalLogL2 :=
  (cc20LogPullback_memLp p).toLp (cc20LogPullback p)

theorem cc20LogPullbackLp_coeFn
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    (cc20LogPullbackLp p : ℝ → ℂ) =ᵐ[volume] cc20LogPullback p :=
  MemLp.coeFn_toLp (cc20LogPullback_memLp p)

theorem exists_cc20LogWindow_containing_logPullback
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ∃ lambda : ℝ,
      1 < lambda ∧
        Function.support (cc20LogPullback p) ⊆ cc20LogWindow lambda := by
  obtain ⟨lambda, hlambda, hwindow⟩ :=
    exists_cc20Window_containing_positiveIntervalCompactTest p
  refine ⟨lambda, hlambda, ?_⟩
  intro t ht
  have hsource : Real.exp t ∈ Set.Icc p.lower p.upper := by
    apply p.support_subset
    simpa [cc20LogPullback, Function.mem_support] using ht
  have hwindow' := hwindow hsource
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  constructor
  · have hlog := Real.log_le_log
      (one_div_pos.mpr hlambda_pos) hwindow'.1
    simpa [cc20LogWindow, Real.log_inv] using hlog
  · have hlog := Real.log_le_log (Real.exp_pos t) hwindow'.2
    simpa [cc20LogWindow] using hlog

theorem cc20LogWindowProjection_eq_self_of_support_subset
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : cc20GlobalLogL2)
    (hsupport : Function.support (u : ℝ → ℂ) ⊆ cc20LogWindow lambda) :
    cc20LogWindowProjection lambda hlambda u = u := by
  rw [Lp.ext_iff]
  filter_upwards [cc20LogWindowProjection_coeFn lambda hlambda u] with t ht
  rw [ht]
  by_cases hwindow : t ∈ cc20LogWindow lambda
  · simp [Set.indicator, hwindow]
  · have hu : (u : ℝ → ℂ) t = 0 := by
      by_contra hne
      exact hwindow (hsupport (by simpa [Function.mem_support] using hne))
    simp [Set.indicator, hwindow, hu]

theorem exists_cc20LogWindowProjection_fix_logPullbackLp
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ∃ lambda : ℝ, ∃ hlambda : 1 < lambda,
      cc20LogWindowProjection lambda hlambda (cc20LogPullbackLp p) =
        cc20LogPullbackLp p := by
  obtain ⟨lambda, hlambda, hsupport⟩ :=
    exists_cc20LogWindow_containing_logPullback p
  refine ⟨lambda, hlambda, ?_⟩
  rw [Lp.ext_iff]
  filter_upwards [cc20LogWindowProjection_coeFn lambda hlambda
      (cc20LogPullbackLp p), cc20LogPullbackLp_coeFn p] with t hproj hpull
  by_cases hwindow : t ∈ cc20LogWindow lambda
  · calc
      (cc20LogWindowProjection lambda hlambda (cc20LogPullbackLp p) : ℝ → ℂ) t =
          (cc20LogWindow lambda).indicator
            (fun t => (cc20LogPullbackLp p : ℝ → ℂ) t) t := hproj
      _ = (cc20LogPullbackLp p : ℝ → ℂ) t := by
        simp [Set.indicator, hwindow]
  · have hzero : cc20LogPullback p t = 0 := by
      by_contra hne
      exact hwindow (hsupport (by simpa [Function.mem_support] using hne))
    calc
      (cc20LogWindowProjection lambda hlambda (cc20LogPullbackLp p) : ℝ → ℂ) t =
          (cc20LogWindow lambda).indicator
            (fun t => (cc20LogPullbackLp p : ℝ → ℂ) t) t := hproj
      _ = 0 := by simp [Set.indicator, hwindow]
      _ = (cc20LogPullbackLp p : ℝ → ℂ) t := by rw [hpull, hzero]

end CC20Concrete
end Source
end ConnesWeilRH
