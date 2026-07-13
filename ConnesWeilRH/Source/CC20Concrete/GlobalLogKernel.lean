/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.HaarLogTransport
import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarCompact
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The ordinary CC20 regular kernel on the common logarithmic carrier

This module transports the same parameterized finite-window kernel action to
the coordinate `rho = exp t`.  It concerns only the ordinary regular part of
the kernel; the diagonal Dirac term and the CC20 trace read-off are not added.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set

abbrev CC20LogWindowPoint (lambda : ℝ) :=
  {t : ℝ // t ∈ cc20LogWindow lambda}

noncomputable def cc20LogPositiveCoordinate (t : ℝ) : PositiveCoordinate :=
  ⟨Real.exp t, Real.exp_pos t⟩

theorem continuous_cc20LogPositiveCoordinate :
    Continuous cc20LogPositiveCoordinate :=
  Real.continuous_exp.subtype_mk _

noncomputable def cc20GlobalLogComplexRegularKernel :
    ContinuousMap (ℝ × ℝ) ℂ where
  toFun p := ((cc20RegularKernel
    (cc20LogPositiveCoordinate p.1, cc20LogPositiveCoordinate p.2) : ℝ) : ℂ)
  continuous_toFun :=
    Complex.continuous_ofReal.comp
      (continuous_cc20RegularKernel.comp
        ((continuous_cc20LogPositiveCoordinate.comp continuous_fst).prodMk
          (continuous_cc20LogPositiveCoordinate.comp continuous_snd)))

noncomputable def cc20GlobalLogComplexRegularProfile :
    ContinuousMap ℝ ℂ where
  toFun r := cc20GlobalLogComplexRegularKernel (r, 0)
  continuous_toFun :=
    cc20GlobalLogComplexRegularKernel.continuous.comp
      (continuous_id.prodMk continuous_const)

theorem cc20GlobalLogComplexRegularProfile_eq_abs_exp (r : ℝ) :
    cc20GlobalLogComplexRegularProfile r =
      ((cc20QDeltaRegularExtension (Real.exp |r|) : ℝ) : ℂ) := by
  change
    ((cc20QDeltaRegularExtension
      (max (Real.exp r / Real.exp 0) (Real.exp 0 / Real.exp r)) : ℝ) : ℂ) = _
  rw [Real.exp_zero, div_one]
  have hinv : 1 / Real.exp r = Real.exp (-r) := by
    rw [one_div, ← Real.exp_neg]
  rw [hinv]
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr, max_eq_left]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hr' : r ≤ 0 := le_of_not_ge hr
    rw [abs_of_nonpos hr', max_eq_right]
    exact Real.exp_le_exp.mpr (by linarith)

theorem cc20GlobalLogComplexRegularKernel_eq_profile
    (t s : ℝ) :
    cc20GlobalLogComplexRegularKernel (t, s) =
      cc20GlobalLogComplexRegularProfile (t - s) := by
  change
    ((cc20QDeltaRegularExtension
      (max (Real.exp t / Real.exp s) (Real.exp s / Real.exp t)) : ℝ) : ℂ) =
      ((cc20QDeltaRegularExtension
        (max (Real.exp (t - s) / Real.exp 0)
          (Real.exp 0 / Real.exp (t - s))) : ℝ) : ℂ)
  congr 2
  rw [Real.exp_zero, div_one, Real.exp_sub]
  congr 1
  field_simp [Real.exp_ne_zero]

theorem cc20GlobalLogComplexRegularKernel_translation_invariant
    (a t s : ℝ) :
    cc20GlobalLogComplexRegularKernel (t + a, s + a) =
      cc20GlobalLogComplexRegularKernel (t, s) := by
  rw [cc20GlobalLogComplexRegularKernel_eq_profile,
    cc20GlobalLogComplexRegularKernel_eq_profile]
  congr 1
  ring

theorem cc20GlobalLogComplexRegularKernel_swap (t s : ℝ) :
    cc20GlobalLogComplexRegularKernel (s, t) =
      cc20GlobalLogComplexRegularKernel (t, s) := by
  change
    ((cc20RegularKernel
      (cc20LogPositiveCoordinate s, cc20LogPositiveCoordinate t) : ℝ) : ℂ) =
      ((cc20RegularKernel
        (cc20LogPositiveCoordinate t, cc20LogPositiveCoordinate s) : ℝ) : ℂ)
  exact congrArg (fun x : ℝ => (x : ℂ))
    (cc20RegularKernel_swap
      (cc20LogPositiveCoordinate t, cc20LogPositiveCoordinate s))

theorem cc20GlobalLogComplexRegularProfile_neg (r : ℝ) :
    cc20GlobalLogComplexRegularProfile (-r) =
      cc20GlobalLogComplexRegularProfile r := by
  change cc20GlobalLogComplexRegularKernel (-r, 0) =
    cc20GlobalLogComplexRegularKernel (r, 0)
  rw [cc20GlobalLogComplexRegularKernel_swap]
  simpa using (cc20GlobalLogComplexRegularKernel_translation_invariant
    r 0 (-r)).symm

theorem cc20GlobalLogComplexRegularProfile_eq_branch_derivatives
    {r : ℝ} (hr : r ≠ 0) :
    cc20GlobalLogComplexRegularProfile r =
      ((-4 * Real.exp |r| * Real.sqrt (Real.exp |r|) *
          cc20DeltaBranchSumDerivative (Real.exp |r|) -
        2 * (Real.exp |r|) ^ 2 * Real.sqrt (Real.exp |r|) *
          cc20DeltaBranchSumSecondDerivative (Real.exp |r|) : ℝ) : ℂ) := by
  have hrho_pos : 0 < Real.exp |r| := Real.exp_pos _
  have hrho_ne_one : Real.exp |r| ≠ 1 := by
    intro h
    have hzero : |r| = 0 := by
      have hlog := congrArg Real.log h
      simpa using hlog
    exact hr (abs_eq_zero.mp hzero)
  rw [cc20GlobalLogComplexRegularProfile_eq_abs_exp,
    cc20QDeltaRegularExtension_of_ne_one hrho_ne_one,
    cc20QDeltaRegularCandidate_eq_branch_derivatives hrho_pos]

noncomputable def cc20LogWindowExpPoint
    (lambda : ℝ) (hlambda : 1 < lambda)
    (t : CC20LogWindowPoint lambda) : CC20WindowPoint lambda := by
  refine ⟨Real.exp t.1, ?_⟩
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  constructor
  · have h := Real.exp_le_exp.mpr t.2.1
    rw [Real.exp_neg, Real.exp_log hlambda_pos] at h
    simpa [one_div] using h
  · have h := Real.exp_le_exp.mpr t.2.2
    simpa [Real.exp_log hlambda_pos] using h

noncomputable def cc20WindowLogPoint
    (lambda : ℝ) (hlambda : 1 < lambda)
    (rho : CC20WindowPoint lambda) : CC20LogWindowPoint lambda := by
  refine ⟨Real.log rho.1, ?_⟩
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hrho_pos : 0 < rho.1 :=
    lt_of_lt_of_le (one_div_pos.mpr hlambda_pos) rho.2.1
  constructor
  · have hlog := Real.log_le_log (one_div_pos.mpr hlambda_pos) rho.2.1
    simpa [Real.log_inv] using hlog
  · exact Real.log_le_log hrho_pos rho.2.2

theorem cc20LogWindowExpPoint_logPoint
    (lambda : ℝ) (hlambda : 1 < lambda)
    (rho : CC20WindowPoint lambda) :
    cc20LogWindowExpPoint lambda hlambda
        (cc20WindowLogPoint lambda hlambda rho) = rho := by
  apply Subtype.ext
  exact Real.exp_log
    (lt_of_lt_of_le
      (one_div_pos.mpr (lt_trans (by norm_num) hlambda)) rho.2.1)

theorem continuous_cc20LogWindowExpPoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Continuous (cc20LogWindowExpPoint lambda hlambda) := by
  unfold cc20LogWindowExpPoint
  apply Continuous.subtype_mk
  exact Real.continuous_exp.comp continuous_subtype_val

theorem continuous_cc20WindowLogPoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Continuous (cc20WindowLogPoint lambda hlambda) := by
  unfold cc20WindowLogPoint
  apply Continuous.subtype_mk
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hlog : ContinuousOn Real.log
      (Set.Icc (1 / lambda) lambda) :=
    Real.continuousOn_log.mono (fun rho hrho =>
      ne_of_gt (lt_of_lt_of_le
        (one_div_pos.mpr hlambda_pos) hrho.1))
  exact continuousOn_iff_continuous_restrict.mp hlog

theorem cc20WindowLogPoint_expPoint
    (lambda : ℝ) (hlambda : 1 < lambda)
    (t : CC20LogWindowPoint lambda) :
    cc20WindowLogPoint lambda hlambda
        (cc20LogWindowExpPoint lambda hlambda t) = t := by
  apply Subtype.ext
  exact Real.log_exp t.1

noncomputable def cc20LogWindowExpHomeomorph
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CC20LogWindowPoint lambda ≃ₜ CC20WindowPoint lambda where
  toEquiv :=
    { toFun := cc20LogWindowExpPoint lambda hlambda
      invFun := cc20WindowLogPoint lambda hlambda
      left_inv := cc20WindowLogPoint_expPoint lambda hlambda
      right_inv := cc20LogWindowExpPoint_logPoint lambda hlambda }
  continuous_toFun := continuous_cc20LogWindowExpPoint lambda hlambda
  continuous_invFun := continuous_cc20WindowLogPoint lambda hlambda

noncomputable def cc20LogWindowBaseMeasure (lambda : ℝ) :
    Measure (CC20LogWindowPoint lambda) :=
  Measure.comap Subtype.val volume

instance cc20LogWindowBaseMeasure_isFinite
    (lambda : ℝ) :
    IsFiniteMeasure (cc20LogWindowBaseMeasure lambda) where
  measure_univ_lt_top := by
    unfold cc20LogWindowBaseMeasure
    rw [
      (MeasurableEmbedding.subtype_coe
        (measurableSet_cc20LogWindow lambda)).comap_apply volume Set.univ,
      Set.image_univ, Subtype.range_coe_subtype]
    change volume (Set.Icc (-Real.log lambda) (Real.log lambda)) < ⊤
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

theorem measurePreserving_cc20LogWindowSubtypeVal
    (lambda : ℝ) :
    MeasurePreserving
      (Subtype.val : CC20LogWindowPoint lambda → ℝ)
      (cc20LogWindowBaseMeasure lambda)
      (volume.restrict (cc20LogWindow lambda)) := by
  exact measurePreserving_subtype_coe
    (μa := volume) (measurableSet_cc20LogWindow lambda)

noncomputable def cc20LogWindowSubtypeValL2Isometry
    (lambda : ℝ) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →ₗᵢ[ℂ]
      Lp ℂ 2 (cc20LogWindowBaseMeasure lambda) :=
  Lp.compMeasurePreservingₗᵢ ℂ Subtype.val
    (measurePreserving_cc20LogWindowSubtypeVal lambda)

theorem surjective_cc20LogWindowSubtypeValL2Isometry
    (lambda : ℝ) :
    Function.Surjective (cc20LogWindowSubtypeValL2Isometry lambda) := by
  intro u
  let huMem : MemLp (u : CC20LogWindowPoint lambda → ℂ) 2
      (cc20LogWindowBaseMeasure lambda) := Lp.memLp u
  let g : CC20LogWindowPoint lambda → ℂ :=
    huMem.aestronglyMeasurable.mk u
  have hgStrong : StronglyMeasurable g :=
    huMem.aestronglyMeasurable.stronglyMeasurable_mk
  obtain ⟨f, hfStrong, hcomp⟩ :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_cc20LogWindow lambda)).exists_stronglyMeasurable_extend
      hgStrong (fun _ => ⟨0⟩)
  have hgMem : MemLp g 2 (cc20LogWindowBaseMeasure lambda) :=
    (memLp_congr_ae huMem.aestronglyMeasurable.ae_eq_mk).mp huMem
  have hfMapMem : MemLp f 2
      (Measure.map (Subtype.val : CC20LogWindowPoint lambda → ℝ)
        (cc20LogWindowBaseMeasure lambda)) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_cc20LogWindow lambda)).memLp_map_measure_iff.mpr
      (by simpa only [hcomp] using hgMem)
  have hfMem : MemLp f 2 (volume.restrict (cc20LogWindow lambda)) := by
    simpa only [(measurePreserving_cc20LogWindowSubtypeVal lambda).map_eq]
      using hfMapMem
  refine ⟨hfMem.toLp f, ?_⟩
  change Lp.compMeasurePreserving Subtype.val
      (measurePreserving_cc20LogWindowSubtypeVal lambda)
      (hfMem.toLp f) = u
  rw [Lp.toLp_compMeasurePreserving]
  calc
    _ = huMem.toLp (u : CC20LogWindowPoint lambda → ℂ) := by
      apply MemLp.toLp_congr
      rw [hcomp]
      exact huMem.aestronglyMeasurable.ae_eq_mk.symm
    _ = u := Lp.toLp_coeFn u huMem

noncomputable def cc20LogWindowSubtypeRestrictedL2IsometryEquiv
    (lambda : ℝ) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cc20LogWindowBaseMeasure lambda) :=
  LinearIsometryEquiv.ofSurjective
    (cc20LogWindowSubtypeValL2Isometry lambda)
    (surjective_cc20LogWindowSubtypeValL2Isometry lambda)

noncomputable def cc20WindowAmbientOfCompactlySupported
    (lambda : ℝ) (f : CompactlySupportedContinuousMap
      (CC20WindowPoint lambda) ℝ) : ℝ → ℝ :=
  fun rho => if hrho : rho ∈ cc20WindowInterval lambda then
    f ⟨rho, hrho⟩ else 0

theorem cc20WindowAmbientOfCompactlySupported_restrict
    (lambda : ℝ) (f : CompactlySupportedContinuousMap
      (CC20WindowPoint lambda) ℝ) :
    (cc20WindowInterval lambda).restrict
        (cc20WindowAmbientOfCompactlySupported lambda f) =
      f := by
  ext rho
  simp [cc20WindowAmbientOfCompactlySupported]

theorem continuousOn_cc20WindowAmbientOfCompactlySupported
    (lambda : ℝ) (f : CompactlySupportedContinuousMap
      (CC20WindowPoint lambda) ℝ) :
    ContinuousOn (cc20WindowAmbientOfCompactlySupported lambda f)
      (cc20WindowInterval lambda) := by
  rw [continuousOn_iff_continuous_restrict]
  rw [cc20WindowAmbientOfCompactlySupported_restrict]
  exact f.continuous_toFun

theorem integral_cc20WindowHaarMeasure_compactlySupported_eq_logInterval
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : CompactlySupportedContinuousMap (CC20WindowPoint lambda) ℝ) :
    (∫ rho, f rho ∂cc20WindowHaarMeasure lambda hlambda) =
      ∫ t in -Real.log lambda..Real.log lambda,
        cc20WindowAmbientOfCompactlySupported lambda f (Real.exp t) := by
  calc
    (∫ rho, f rho ∂cc20WindowHaarMeasure lambda hlambda) =
        ∫ rho, cc20WindowAmbientOfCompactlySupported lambda f rho.1
          ∂cc20WindowHaarMeasure lambda hlambda := by
      apply integral_congr_ae
      filter_upwards with rho
      have hrestrict := congrArg
        (fun g => g rho)
        (cc20WindowAmbientOfCompactlySupported_restrict lambda f)
      exact hrestrict.symm
    _ = ∫ t in -Real.log lambda..Real.log lambda,
        cc20WindowAmbientOfCompactlySupported lambda f (Real.exp t) :=
      integral_cc20WindowHaarMeasure_eq_logInterval_real_of_continuousOn
        lambda hlambda (cc20WindowAmbientOfCompactlySupported lambda f)
        (continuousOn_cc20WindowAmbientOfCompactlySupported lambda f)

theorem integral_cc20LogWindowBaseMeasure_comp_exp_eq_logInterval
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : CompactlySupportedContinuousMap (CC20WindowPoint lambda) ℝ) :
    (∫ t, f (cc20LogWindowExpPoint lambda hlambda t)
        ∂cc20LogWindowBaseMeasure lambda) =
      ∫ t in -Real.log lambda..Real.log lambda,
        cc20WindowAmbientOfCompactlySupported lambda f (Real.exp t) := by
  let ambient : ℝ → ℝ := fun t =>
    cc20WindowAmbientOfCompactlySupported lambda f (Real.exp t)
  calc
    (∫ t, f (cc20LogWindowExpPoint lambda hlambda t)
        ∂cc20LogWindowBaseMeasure lambda) =
        ∫ t, ambient t.1 ∂cc20LogWindowBaseMeasure lambda := by
      apply integral_congr_ae
      filter_upwards with t
      have hrestrict := congrArg
        (fun g => g (cc20LogWindowExpPoint lambda hlambda t))
        (cc20WindowAmbientOfCompactlySupported_restrict lambda f)
      exact hrestrict.symm
    _ = ∫ t in cc20LogWindow lambda, ambient t := by
      exact integral_subtype_comap (measurableSet_cc20LogWindow lambda) ambient
    _ = ∫ t in -Real.log lambda..Real.log lambda, ambient t := by
      have hle : -Real.log lambda ≤ Real.log lambda := by
        linarith [Real.log_pos hlambda]
      rw [cc20LogWindow, intervalIntegral.integral_of_le hle,
        integral_Icc_eq_integral_Ioc]

theorem map_cc20LogWindowBaseMeasure_exp_eq_windowHaarMeasure
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Measure.map (cc20LogWindowExpPoint lambda hlambda)
        (cc20LogWindowBaseMeasure lambda) =
      cc20WindowHaarMeasure lambda hlambda := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  calc
    (∫ rho, f rho
        ∂Measure.map (cc20LogWindowExpPoint lambda hlambda)
          (cc20LogWindowBaseMeasure lambda)) =
        ∫ t, f (cc20LogWindowExpPoint lambda hlambda t)
          ∂cc20LogWindowBaseMeasure lambda :=
      (cc20LogWindowExpHomeomorph lambda hlambda).isClosedEmbedding.integral_map f
    _ = ∫ t in -Real.log lambda..Real.log lambda,
        cc20WindowAmbientOfCompactlySupported lambda f (Real.exp t) :=
      integral_cc20LogWindowBaseMeasure_comp_exp_eq_logInterval lambda hlambda f
    _ = ∫ rho, f rho ∂cc20WindowHaarMeasure lambda hlambda :=
      (integral_cc20WindowHaarMeasure_compactlySupported_eq_logInterval
        lambda hlambda f).symm

theorem measurePreserving_cc20LogWindowExpPoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    MeasurePreserving (cc20LogWindowExpPoint lambda hlambda)
      (cc20LogWindowBaseMeasure lambda)
      (cc20WindowHaarMeasure lambda hlambda) where
  measurable := (continuous_cc20LogWindowExpPoint lambda hlambda).measurable
  map_eq := map_cc20LogWindowBaseMeasure_exp_eq_windowHaarMeasure lambda hlambda

theorem measurePreserving_cc20WindowLogPoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    MeasurePreserving (cc20WindowLogPoint lambda hlambda)
      (cc20WindowHaarMeasure lambda hlambda)
      (cc20LogWindowBaseMeasure lambda) :=
  MeasurePreserving.symm
    (cc20LogWindowExpHomeomorph lambda hlambda).toMeasurableEquiv
    (measurePreserving_cc20LogWindowExpPoint lambda hlambda)

noncomputable def cc20WindowHaarLogL2IsometryEquiv
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cc20LogWindowBaseMeasure lambda) where
  toLinearEquiv :=
    { toLinearMap := (Lp.compMeasurePreservingₗᵢ ℂ
        (cc20LogWindowExpPoint lambda hlambda)
        (measurePreserving_cc20LogWindowExpPoint lambda hlambda)).toLinearMap
      invFun := Lp.compMeasurePreserving
        (cc20WindowLogPoint lambda hlambda)
        (measurePreserving_cc20WindowLogPoint lambda hlambda)
      left_inv := by
        intro u
        change Lp.compMeasurePreserving
          (cc20WindowLogPoint lambda hlambda)
          (measurePreserving_cc20WindowLogPoint lambda hlambda)
          (Lp.compMeasurePreserving
            (cc20LogWindowExpPoint lambda hlambda)
            (measurePreserving_cc20LogWindowExpPoint lambda hlambda) u) = u
        rw [← Lp.compMeasurePreserving_comp_apply u
          (measurePreserving_cc20LogWindowExpPoint lambda hlambda)
          (measurePreserving_cc20WindowLogPoint lambda hlambda)]
        have hfun :
            cc20LogWindowExpPoint lambda hlambda ∘
                cc20WindowLogPoint lambda hlambda = id := by
          funext rho
          exact cc20LogWindowExpPoint_logPoint lambda hlambda rho
        simpa only [hfun] using Lp.compMeasurePreserving_id_apply u
      right_inv := by
        intro u
        change Lp.compMeasurePreserving
          (cc20LogWindowExpPoint lambda hlambda)
          (measurePreserving_cc20LogWindowExpPoint lambda hlambda)
          (Lp.compMeasurePreserving
            (cc20WindowLogPoint lambda hlambda)
            (measurePreserving_cc20WindowLogPoint lambda hlambda) u) = u
        rw [← Lp.compMeasurePreserving_comp_apply u
          (measurePreserving_cc20WindowLogPoint lambda hlambda)
          (measurePreserving_cc20LogWindowExpPoint lambda hlambda)]
        have hfun :
            cc20WindowLogPoint lambda hlambda ∘
                cc20LogWindowExpPoint lambda hlambda = id := by
          funext t
          exact cc20WindowLogPoint_expPoint lambda hlambda t
        simpa only [hfun] using Lp.compMeasurePreserving_id_apply u }
  norm_map' := Lp.norm_compMeasurePreserving
    (hf := measurePreserving_cc20LogWindowExpPoint lambda hlambda)

noncomputable def cc20WindowHaarRestrictedLogL2IsometryEquiv
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  (cc20WindowHaarLogL2IsometryEquiv lambda hlambda).trans
    (cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda).symm

noncomputable def cc20WindowLogRestriction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) : ContinuousMap (CC20WindowPoint lambda) ℂ where
  toFun rho := u (Real.log rho.1)
  continuous_toFun :=
    u.continuous.comp
      (Real.continuous_log'.comp
        (continuous_cc20WindowPositiveCoordinate lambda hlambda))

theorem cc20WindowHaarRestrictedLogL2IsometryEquiv_apply_logRestriction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
        (ContinuousMap.toLp 2
          (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u.toContinuousMap)) =
      BoundedContinuousFunction.toLp 2
        (volume.restrict (cc20LogWindow lambda)) ℂ u := by
  apply (cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda).injective
  change
    cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda
        (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
          (ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u.toContinuousMap))) =
      cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda
        (BoundedContinuousFunction.toLp 2
          (volume.restrict (cc20LogWindow lambda)) ℂ u)
  simp only [cc20WindowHaarRestrictedLogL2IsometryEquiv,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change
    Lp.compMeasurePreserving (cc20LogWindowExpPoint lambda hlambda)
        (measurePreserving_cc20LogWindowExpPoint lambda hlambda)
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u.toContinuousMap)) =
      Lp.compMeasurePreserving (Subtype.val : CC20LogWindowPoint lambda → ℝ)
        (measurePreserving_cc20LogWindowSubtypeVal lambda)
        (BoundedContinuousFunction.toLp 2
          (volume.restrict (cc20LogWindow lambda)) ℂ u)
  rw [Lp.ext_iff]
  have hleft := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
      (cc20WindowLogRestriction lambda hlambda u.toContinuousMap))
    (measurePreserving_cc20LogWindowExpPoint lambda hlambda)
  have hleft_core :=
    (measurePreserving_cc20LogWindowExpPoint lambda hlambda).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (cc20WindowHaarMeasure lambda hlambda)
        (𝕜 := ℂ)
        (cc20WindowLogRestriction lambda hlambda u.toContinuousMap))
  have hright := Lp.coeFn_compMeasurePreserving
    (BoundedContinuousFunction.toLp 2
      (volume.restrict (cc20LogWindow lambda)) ℂ u)
    (measurePreserving_cc20LogWindowSubtypeVal lambda)
  have hright_core :=
    (measurePreserving_cc20LogWindowSubtypeVal lambda).quasiMeasurePreserving.ae_eq_comp
      (BoundedContinuousFunction.coeFn_toLp 2
        (volume.restrict (cc20LogWindow lambda)) ℂ u)
  filter_upwards [hleft, hleft_core, hright, hright_core] with
    t htleft hcore htright hrightcore
  rw [htleft, hcore, htright, hrightcore]
  simp [Function.comp_apply, cc20WindowLogRestriction, cc20LogWindowExpPoint]

theorem cc20WindowPositiveCoordinate_expPoint
    (lambda : ℝ) (hlambda : 1 < lambda)
    (t : CC20LogWindowPoint lambda) :
    cc20WindowPositiveCoordinate lambda hlambda
        (cc20LogWindowExpPoint lambda hlambda t) =
      cc20LogPositiveCoordinate t.1 := by
  apply Subtype.ext
  rfl

theorem cc20WindowComplexRegularKernel_eq_logKernel
    (lambda : ℝ) (hlambda : 1 < lambda)
    (x y : CC20WindowPoint lambda) :
    cc20WindowComplexRegularKernel lambda hlambda (x, y) =
      cc20GlobalLogComplexRegularKernel (Real.log x.1, Real.log y.1) := by
  change ((cc20RegularKernel
      (cc20WindowPositiveCoordinate lambda hlambda x,
        cc20WindowPositiveCoordinate lambda hlambda y) : ℝ) : ℂ) =
    ((cc20RegularKernel
      (cc20LogPositiveCoordinate (Real.log x.1),
        cc20LogPositiveCoordinate (Real.log y.1)) : ℝ) : ℂ)
  congr
  · apply Subtype.ext
    simpa [cc20WindowPositiveCoordinate, cc20LogPositiveCoordinate] using
      (Real.exp_log
        (cc20WindowPositiveCoordinate lambda hlambda x).2).symm
  · apply Subtype.ext
    simpa [cc20WindowPositiveCoordinate, cc20LogPositiveCoordinate] using
      (Real.exp_log
        (cc20WindowPositiveCoordinate lambda hlambda y).2).symm

noncomputable def cc20GlobalLogWindowRegularAction
    (lambda : ℝ) (t : ℝ) (u : ContinuousMap ℝ ℂ) : ℂ :=
  ∫ s in -Real.log lambda..Real.log lambda,
    cc20GlobalLogComplexRegularKernel (t, s) * u s

noncomputable def cc20GlobalLogWindowRegularActionContinuous
    (lambda : ℝ) (u : ContinuousMap ℝ ℂ) : ContinuousMap ℝ ℂ where
  toFun t := cc20GlobalLogWindowRegularAction lambda t u
  continuous_toFun := by
    unfold cc20GlobalLogWindowRegularAction
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop

@[simp]
theorem cc20GlobalLogWindowRegularActionContinuous_apply
    (lambda : ℝ) (u : ContinuousMap ℝ ℂ) (t : ℝ) :
    cc20GlobalLogWindowRegularActionContinuous lambda u t =
    cc20GlobalLogWindowRegularAction lambda t u := rfl

theorem cc20GlobalLogWindowRegularActionContinuous_add
    (lambda : ℝ) (u v : ContinuousMap ℝ ℂ) :
    cc20GlobalLogWindowRegularActionContinuous lambda (u + v) =
      cc20GlobalLogWindowRegularActionContinuous lambda u +
        cc20GlobalLogWindowRegularActionContinuous lambda v := by
  ext t
  change
    (∫ s in -Real.log lambda..Real.log lambda,
        cc20GlobalLogComplexRegularKernel (t, s) * (u + v) s) =
      (∫ s in -Real.log lambda..Real.log lambda,
        cc20GlobalLogComplexRegularKernel (t, s) * u s) +
        ∫ s in -Real.log lambda..Real.log lambda,
          cc20GlobalLogComplexRegularKernel (t, s) * v s
  rw [show (fun s => cc20GlobalLogComplexRegularKernel (t, s) * (u + v) s) =
      (fun s => cc20GlobalLogComplexRegularKernel (t, s) * u s +
        cc20GlobalLogComplexRegularKernel (t, s) * v s) by
        funext s; simp only [ContinuousMap.add_apply, mul_add]]
  exact intervalIntegral.integral_add
    ((cc20GlobalLogComplexRegularKernel.continuous.comp
      (continuous_const.prodMk continuous_id)).mul u.continuous
      |>.intervalIntegrable (μ := volume) _ _)
    ((cc20GlobalLogComplexRegularKernel.continuous.comp
      (continuous_const.prodMk continuous_id)).mul v.continuous
      |>.intervalIntegrable (μ := volume) _ _)

theorem cc20GlobalLogWindowRegularActionContinuous_smul
    (lambda : ℝ) (c : ℂ) (u : ContinuousMap ℝ ℂ) :
    cc20GlobalLogWindowRegularActionContinuous lambda (c • u) =
      c • cc20GlobalLogWindowRegularActionContinuous lambda u := by
  ext t
  change
    (∫ s in -Real.log lambda..Real.log lambda,
        cc20GlobalLogComplexRegularKernel (t, s) * (c • u) s) =
      c • ∫ s in -Real.log lambda..Real.log lambda,
        cc20GlobalLogComplexRegularKernel (t, s) * u s
  rw [show (fun s => cc20GlobalLogComplexRegularKernel (t, s) * (c • u) s) =
      (fun s => c • (cc20GlobalLogComplexRegularKernel (t, s) * u s)) by
        funext s; simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
          mul_comm]]
  exact intervalIntegral.integral_smul c _

theorem cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
    (lambda : ℝ) (_hlambda : 1 < lambda) (u : ContinuousMap ℝ ℂ) :
    MemLp (cc20GlobalLogWindowRegularActionContinuous lambda u : ℝ → ℂ)
      2 (volume.restrict (cc20LogWindow lambda)) := by
  let action := cc20GlobalLogWindowRegularActionContinuous lambda u
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (cc20LogWindow lambda)).bddAbove_image
      action.continuous.norm.continuousOn
  letI : IsFiniteMeasure (volume.restrict (cc20LogWindow lambda)) := by
    rw [cc20LogWindow]
    infer_instance
  apply MemLp.of_bound action.continuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurableSet_cc20LogWindow lambda)] with t ht
  exact hC ⟨t, ht, rfl⟩

set_option maxHeartbeats 400000 in
-- Elaboration of the dependent `MemLp.toLp` witness needs a wider local budget.
noncomputable def cc20GlobalLogWindowRegularActionToLp
    (lambda : ℝ) (hlambda : 1 < lambda) (u : ContinuousMap ℝ ℂ) :
    cc20GlobalLogL2 :=
  ((memLp_indicator_iff_restrict (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda u)).toLp
      ((cc20LogWindow lambda).indicator
      (cc20GlobalLogWindowRegularActionContinuous lambda u))

theorem cc20GlobalLogWindowContinuousInput_memLp_restrict
    (lambda : ℝ) (_hlambda : 1 < lambda) (u : ContinuousMap ℝ ℂ) :
    MemLp (u : ℝ → ℂ) 2 (volume.restrict (cc20LogWindow lambda)) := by
  letI : IsFiniteMeasure (volume.restrict (cc20LogWindow lambda)) := by
    rw [cc20LogWindow]
    infer_instance
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (cc20LogWindow lambda)).bddAbove_image
      u.continuous.norm.continuousOn
  apply MemLp.of_bound u.continuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurableSet_cc20LogWindow lambda)] with t ht
  exact hC ⟨t, ht, rfl⟩

noncomputable def cc20GlobalLogWindowContinuousInputToLp
    (lambda : ℝ) (hlambda : 1 < lambda) (u : ContinuousMap ℝ ℂ) :
    cc20GlobalLogL2 :=
  ((memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowContinuousInput_memLp_restrict
        lambda hlambda u)).toLp
    ((cc20LogWindow lambda).indicator u)

theorem norm_cc20GlobalLogWindowContinuousInputToLp_sq
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    ‖cc20GlobalLogWindowContinuousInputToLp lambda hlambda u‖ ^ 2 =
      ∫ t in -Real.log lambda..Real.log lambda, ‖u t‖ ^ 2 := by
  let hInput : MemLp ((cc20LogWindow lambda).indicator u) 2 volume :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowContinuousInput_memLp_restrict
        lambda hlambda u)
  change ‖hInput.toLp ((cc20LogWindow lambda).indicator u)‖ ^ 2 = _
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hInput)]
  rw [hInput.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hIntegral :
      (∫ t, ‖(cc20LogWindow lambda).indicator u t‖ ^ 2) =
        ∫ t in -Real.log lambda..Real.log lambda, ‖u t‖ ^ 2 := by
    calc
      (∫ t, ‖(cc20LogWindow lambda).indicator u t‖ ^ 2) =
          ∫ t, (cc20LogWindow lambda).indicator
            (fun s => ‖u s‖ ^ 2) t := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ cc20LogWindow lambda <;>
          simp [Set.indicator, ht]
      _ = ∫ t in cc20LogWindow lambda, ‖u t‖ ^ 2 := by
        rw [← integral_indicator (measurableSet_cc20LogWindow lambda)]
      _ = ∫ t in -Real.log lambda..Real.log lambda, ‖u t‖ ^ 2 := by
        rw [cc20LogWindow, integral_Icc_eq_integral_Ioc]
        rw [← intervalIntegral.integral_of_le]
        exact le_of_lt (by linarith [cc20LogWindow_log_pos lambda hlambda])
  have hnonneg :
      0 ≤ ∫ t, ‖(cc20LogWindow lambda).indicator u t‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  calc
    (ENNReal.ofReal
        ((∫ t, ‖(cc20LogWindow lambda).indicator u t‖ ^ 2) ^
          (1 / (2 : ℝ)))).toReal ^ 2 =
        ((∫ t, ‖(cc20LogWindow lambda).indicator u t‖ ^ 2) ^
          (1 / (2 : ℝ))) ^ 2 := by
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    _ = ∫ t, ‖(cc20LogWindow lambda).indicator u t‖ ^ 2 := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
    _ = _ := hIntegral

theorem cc20GlobalLogWindowRegularActionToLp_add
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u v : ContinuousMap ℝ ℂ) :
    cc20GlobalLogWindowRegularActionToLp lambda hlambda (u + v) =
      cc20GlobalLogWindowRegularActionToLp lambda hlambda u +
        cc20GlobalLogWindowRegularActionToLp lambda hlambda v := by
  let hU :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda u)
  let hV :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda v)
  let hUV :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda (u + v))
  change hUV.toLp
      ((cc20LogWindow lambda).indicator
        (cc20GlobalLogWindowRegularActionContinuous lambda (u + v))) =
    hU.toLp ((cc20LogWindow lambda).indicator
        (cc20GlobalLogWindowRegularActionContinuous lambda u)) +
      hV.toLp ((cc20LogWindow lambda).indicator
        (cc20GlobalLogWindowRegularActionContinuous lambda v))
  rw [← MemLp.toLp_add hU hV]
  apply MemLp.toLp_congr hUV (hU.add hV)
  filter_upwards [] with t
  rw [cc20GlobalLogWindowRegularActionContinuous_add]
  by_cases ht : t ∈ cc20LogWindow lambda <;> simp [Set.indicator, ht]

theorem cc20GlobalLogWindowRegularActionToLp_smul
    (lambda : ℝ) (hlambda : 1 < lambda) (c : ℂ)
    (u : ContinuousMap ℝ ℂ) :
    cc20GlobalLogWindowRegularActionToLp lambda hlambda (c • u) =
      c • cc20GlobalLogWindowRegularActionToLp lambda hlambda u := by
  let hU :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda u)
  let hCU :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda (c • u))
  change hCU.toLp
      ((cc20LogWindow lambda).indicator
        (cc20GlobalLogWindowRegularActionContinuous lambda (c • u))) =
    c • hU.toLp ((cc20LogWindow lambda).indicator
      (cc20GlobalLogWindowRegularActionContinuous lambda u))
  rw [← MemLp.toLp_const_smul c hU]
  apply MemLp.toLp_congr hCU (hU.const_smul c)
  filter_upwards [] with t
  rw [cc20GlobalLogWindowRegularActionContinuous_smul]
  by_cases ht : t ∈ cc20LogWindow lambda <;> simp [Set.indicator, ht]

theorem norm_cc20GlobalLogWindowRegularActionToLp_sq
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    ‖cc20GlobalLogWindowRegularActionToLp lambda hlambda u‖ ^ 2 =
      ∫ t in -Real.log lambda..Real.log lambda,
        ‖cc20GlobalLogWindowRegularActionContinuous lambda u t‖ ^ 2 := by
  let action := cc20GlobalLogWindowRegularActionContinuous lambda u
  let hAction : MemLp ((cc20LogWindow lambda).indicator action) 2 volume :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda u)
  change ‖hAction.toLp ((cc20LogWindow lambda).indicator action)‖ ^ 2 = _
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hAction)]
  rw [hAction.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hIntegral :
      (∫ t, ‖(cc20LogWindow lambda).indicator action t‖ ^ 2) =
        ∫ t in -Real.log lambda..Real.log lambda, ‖action t‖ ^ 2 := by
    calc
      (∫ t, ‖(cc20LogWindow lambda).indicator action t‖ ^ 2) =
          ∫ t, (cc20LogWindow lambda).indicator
            (fun s => ‖action s‖ ^ 2) t := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ cc20LogWindow lambda <;>
          simp [Set.indicator, ht]
      _ = ∫ t in cc20LogWindow lambda, ‖action t‖ ^ 2 := by
        rw [← integral_indicator (measurableSet_cc20LogWindow lambda)]
      _ = ∫ t in -Real.log lambda..Real.log lambda, ‖action t‖ ^ 2 := by
        rw [cc20LogWindow, integral_Icc_eq_integral_Ioc]
        rw [← intervalIntegral.integral_of_le]
        exact le_of_lt (by linarith [cc20LogWindow_log_pos lambda hlambda])
  have hnonneg :
      0 ≤ ∫ t, ‖(cc20LogWindow lambda).indicator action t‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  calc
    (ENNReal.ofReal
        ((∫ t, ‖(cc20LogWindow lambda).indicator action t‖ ^ 2) ^
          (1 / (2 : ℝ)))).toReal ^ 2 =
        ((∫ t, ‖(cc20LogWindow lambda).indicator action t‖ ^ 2) ^
          (1 / (2 : ℝ))) ^ 2 := by
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    _ = ∫ t, ‖(cc20LogWindow lambda).indicator action t‖ ^ 2 := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
    _ = _ := by simpa [action] using hIntegral

theorem cc20GlobalLogWindowRegularAction_eq_of_support_subset
    (lambda mu : ℝ) (hlambda : 1 < lambda) (hmu : 1 < mu)
    (hle : lambda ≤ mu) (t : ℝ) (u : ContinuousMap ℝ ℂ)
    (hsupport : Function.support u ⊆ cc20LogWindow lambda) :
    cc20GlobalLogWindowRegularAction mu t u =
      cc20GlobalLogWindowRegularAction lambda t u := by
  let integrand : ℝ → ℂ := fun s =>
    cc20GlobalLogComplexRegularKernel (t, s) * u s
  have hcont : Continuous integrand := by
    exact (cc20GlobalLogComplexRegularKernel.continuous.comp
      (continuous_const.prodMk continuous_id)).mul u.continuous
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hmu_pos : 0 < mu := lt_trans (by norm_num) hmu
  have hlog : Real.log lambda ≤ Real.log mu :=
    Real.log_le_log hlambda_pos hle
  have hleft : (∫ s in -Real.log mu..-Real.log lambda, integrand s) = 0 := by
    have hzero := intervalIntegral.integral_congr_ae
      (f := integrand) (g := fun _ => (0 : ℂ)) (μ := volume)
      (a := -Real.log mu) (b := -Real.log lambda) ?_
    simpa using hzero
    filter_upwards
      [show ∀ᵐ s : ℝ ∂volume, s ≠ -Real.log lambda by
        simp [ae_iff, measure_singleton]] with s hsne hs
    have hs' : s ∈ Set.Ioc (-Real.log mu) (-Real.log lambda) := by
      simpa [uIoc, hlog] using hs
    have hnot : s ∉ cc20LogWindow lambda := by
      intro hswindow
      have hslt : s < -Real.log lambda :=
        lt_of_le_of_ne hs'.2 hsne
      exact (not_lt_of_ge hswindow.1) hslt
    have huzero : u s = 0 := by
      by_contra hne
      exact hnot (hsupport (by simpa [Function.mem_support] using hne))
    simp [integrand, huzero]
  have hright : (∫ s in Real.log lambda..Real.log mu, integrand s) = 0 := by
    have hzero := intervalIntegral.integral_congr_ae
      (f := integrand) (g := fun _ => (0 : ℂ)) (μ := volume)
      (a := Real.log lambda) (b := Real.log mu) ?_
    simpa using hzero
    filter_upwards
      [show ∀ᵐ s : ℝ ∂volume, s ≠ Real.log lambda by
        simp [ae_iff, measure_singleton]] with s hsne hs
    have hs' : s ∈ Set.Ioc (Real.log lambda) (Real.log mu) := by
      simpa [uIoc, hlog] using hs
    have hnot : s ∉ cc20LogWindow lambda := by
      intro hswindow
      linarith [hs'.1, hswindow.2, hsne]
    have huzero : u s = 0 := by
      by_contra hne
      exact hnot (hsupport (by simpa [Function.mem_support] using hne))
    simp [integrand, huzero]
  have hsplit :
      (∫ s in -Real.log mu..-Real.log lambda, integrand s) +
          (∫ s in -Real.log lambda..Real.log mu, integrand s) =
        ∫ s in -Real.log mu..Real.log mu, integrand s :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) _ _)
      (hcont.intervalIntegrable (μ := volume) _ _)
  have hsplit_right :
      (∫ s in -Real.log lambda..Real.log lambda, integrand s) +
          (∫ s in Real.log lambda..Real.log mu, integrand s) =
        ∫ s in -Real.log lambda..Real.log mu, integrand s :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) _ _)
      (hcont.intervalIntegrable (μ := volume) _ _)
  change (∫ s in -Real.log mu..Real.log mu, integrand s) =
    ∫ s in -Real.log lambda..Real.log lambda, integrand s
  calc
    (∫ s in -Real.log mu..Real.log mu, integrand s) =
        (∫ s in -Real.log mu..-Real.log lambda, integrand s) +
          (∫ s in -Real.log lambda..Real.log mu, integrand s) := hsplit.symm
    _ = (∫ s in -Real.log lambda..Real.log lambda, integrand s) := by
      rw [hleft, ← hsplit_right, hright]
      simp

theorem cc20GlobalLogWindowRegularAction_eq_profile
    (lambda t : ℝ) (u : ContinuousMap ℝ ℂ) :
    cc20GlobalLogWindowRegularAction lambda t u =
      ∫ s in -Real.log lambda..Real.log lambda,
        cc20GlobalLogComplexRegularProfile (t - s) * u s := by
  apply intervalIntegral.integral_congr
  intro s _hs
  change cc20GlobalLogComplexRegularKernel (t, s) * u s =
    cc20GlobalLogComplexRegularProfile (t - s) * u s
  rw [cc20GlobalLogComplexRegularKernel_eq_profile]

theorem continuousOn_cc20LogKernelActionIntegrand
    (lambda : ℝ) (hlambda : 1 < lambda)
    (t : ℝ) (u : ContinuousMap ℝ ℂ) :
    ContinuousOn
      (fun rho : ℝ =>
        cc20GlobalLogComplexRegularKernel (t, Real.log rho) *
          u (Real.log rho))
      (Set.Icc (1 / lambda) lambda) := by
  have hlog : ContinuousOn Real.log (Set.Icc (1 / lambda) lambda) :=
    Real.continuousOn_log.mono (fun rho hrho => by
      have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
      exact ne_of_gt (lt_of_lt_of_le
        (one_div_pos.mpr hlambda_pos) hrho.1))
  have hpair : ContinuousOn (fun rho : ℝ => (t, Real.log rho))
      (Set.Icc (1 / lambda) lambda) :=
    continuousOn_const.prodMk hlog
  exact
    (cc20GlobalLogComplexRegularKernel.continuous.comp_continuousOn hpair).mul
      (u.continuous.comp_continuousOn hlog)

theorem cc20WindowSourceHaarAction_eq_globalLogWindowRegularAction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (t : CC20LogWindowPoint lambda) (u : ContinuousMap ℝ ℂ) :
    cc20WindowSourceHaarAction lambda hlambda
        (cc20WindowLogRestriction lambda hlambda u)
        (cc20LogWindowExpPoint lambda hlambda t) =
      cc20GlobalLogWindowRegularAction lambda t.1 u := by
  let integrand : ℝ → ℂ := fun rho =>
    cc20GlobalLogComplexRegularKernel (t.1, Real.log rho) *
      u (Real.log rho)
  calc
    cc20WindowSourceHaarAction lambda hlambda
        (cc20WindowLogRestriction lambda hlambda u)
        (cc20LogWindowExpPoint lambda hlambda t) =
        ∫ rho, integrand rho.1
          ∂cc20WindowHaarMeasure lambda hlambda := by
      apply integral_congr_ae
      filter_upwards with rho
      rw [cc20WindowComplexRegularKernel_eq_logKernel]
      simp [cc20WindowLogRestriction, integrand, cc20LogWindowExpPoint]
    _ = ∫ s in -Real.log lambda..Real.log lambda,
          integrand (Real.exp s) := by
      exact integral_cc20WindowHaarMeasure_eq_logInterval_of_continuousOn
        lambda hlambda integrand
          (continuousOn_cc20LogKernelActionIntegrand lambda hlambda t.1 u)
    _ = cc20GlobalLogWindowRegularAction lambda t.1 u := by
      apply intervalIntegral.integral_congr
      intro s _hs
      simp [integrand]

theorem cc20WindowHaarComplexKernelCoefficient_logRestriction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) (rho : CC20WindowPoint lambda) :
    cc20WindowHaarComplexKernelCoefficient lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u)) rho =
      cc20GlobalLogWindowRegularAction lambda (Real.log rho.1) u := by
  rw [cc20WindowHaarComplexKernelCoefficient_continuous_input]
  have h := cc20WindowSourceHaarAction_eq_globalLogWindowRegularAction
    lambda hlambda (cc20WindowLogPoint lambda hlambda rho) u
  rw [cc20LogWindowExpPoint_logPoint] at h
  simpa [cc20WindowLogPoint] using h

theorem cc20WindowHaarComplexKernelCoefficient_logRestriction_eq
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    cc20WindowHaarComplexKernelCoefficient lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u)) =
      cc20WindowLogRestriction lambda hlambda
        (cc20GlobalLogWindowRegularActionContinuous lambda u) := by
  ext rho
  exact cc20WindowHaarComplexKernelCoefficient_logRestriction
    lambda hlambda u rho

theorem cc20WindowHaarComplexL2Operator_logRestriction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    cc20WindowHaarComplexL2Operator lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u)) =
      ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
        (cc20WindowLogRestriction lambda hlambda
          (cc20GlobalLogWindowRegularActionContinuous lambda u)) := by
  rw [cc20WindowHaarComplexL2Operator_apply,
    cc20WindowHaarComplexKernelCoefficient_logRestriction_eq]

theorem norm_cc20WindowHaarComplexL2Operator_logRestriction_eq_global
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    ‖cc20WindowHaarComplexL2Operator lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u))‖ =
      ‖cc20GlobalLogWindowRegularActionToLp lambda hlambda u‖ := by
  let action := cc20GlobalLogWindowRegularActionContinuous lambda u
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hlog : ContinuousOn Real.log (Set.Icc (1 / lambda) lambda) :=
    Real.continuousOn_log.mono (fun rho hrho => by
      exact ne_of_gt (lt_of_lt_of_le
        (one_div_pos.mpr hlambda_pos) hrho.1))
  have hcontinuous : ContinuousOn
      (fun rho : ℝ => ‖action (Real.log rho)‖ ^ 2)
      (Set.Icc (1 / lambda) lambda) :=
    (action.continuous.comp_continuousOn hlog).norm.pow 2
  have htransport :=
    integral_cc20WindowHaarMeasure_eq_logInterval_real_of_continuousOn
      lambda hlambda (fun rho : ℝ => ‖action (Real.log rho)‖ ^ 2)
        hcontinuous
  have hsq :
      ‖cc20WindowHaarComplexL2Operator lambda hlambda
          (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u))‖ ^ 2 =
        ‖cc20GlobalLogWindowRegularActionToLp lambda hlambda u‖ ^ 2 := by
    calc
      ‖cc20WindowHaarComplexL2Operator lambda hlambda
          (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u))‖ ^ 2 =
          ∫ rho, ‖cc20WindowLogRestriction lambda hlambda action rho‖ ^ 2
            ∂cc20WindowHaarMeasure lambda hlambda := by
        rw [cc20WindowHaarComplexL2Operator_logRestriction,
          norm_cc20WindowHaarComplex_toLp_continuous_sq]
      _ = ∫ t in -Real.log lambda..Real.log lambda, ‖action t‖ ^ 2 := by
        change
          (∫ rho, ‖action (Real.log rho.1)‖ ^ 2
            ∂cc20WindowHaarMeasure lambda hlambda) = _
        rw [htransport]
        apply intervalIntegral.integral_congr
        intro t _ht
        simp only [Real.log_exp]
      _ = ‖cc20GlobalLogWindowRegularActionToLp lambda hlambda u‖ ^ 2 :=
        (norm_cc20GlobalLogWindowRegularActionToLp_sq
          lambda hlambda u).symm
  nlinarith [norm_nonneg
      (cc20WindowHaarComplexL2Operator lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u))),
    norm_nonneg (cc20GlobalLogWindowRegularActionToLp lambda hlambda u)]

theorem norm_cc20WindowHaarComplex_toLp_logRestriction_eq_global_input
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    ‖ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
        (cc20WindowLogRestriction lambda hlambda u)‖ =
      ‖cc20GlobalLogWindowContinuousInputToLp lambda hlambda u‖ := by
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hlog : ContinuousOn Real.log (Set.Icc (1 / lambda) lambda) :=
    Real.continuousOn_log.mono (fun rho hrho => by
      exact ne_of_gt (lt_of_lt_of_le
        (one_div_pos.mpr hlambda_pos) hrho.1))
  have hcontinuous : ContinuousOn
      (fun rho : ℝ => ‖u (Real.log rho)‖ ^ 2)
      (Set.Icc (1 / lambda) lambda) :=
    (u.continuous.comp_continuousOn hlog).norm.pow 2
  have htransport :=
    integral_cc20WindowHaarMeasure_eq_logInterval_real_of_continuousOn
      lambda hlambda (fun rho : ℝ => ‖u (Real.log rho)‖ ^ 2)
        hcontinuous
  have hsq :
      ‖ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u)‖ ^ 2 =
        ‖cc20GlobalLogWindowContinuousInputToLp lambda hlambda u‖ ^ 2 := by
    calc
      ‖ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u)‖ ^ 2 =
          ∫ rho, ‖cc20WindowLogRestriction lambda hlambda u rho‖ ^ 2
            ∂cc20WindowHaarMeasure lambda hlambda :=
        norm_cc20WindowHaarComplex_toLp_continuous_sq
          lambda hlambda (cc20WindowLogRestriction lambda hlambda u)
      _ = ∫ t in -Real.log lambda..Real.log lambda, ‖u t‖ ^ 2 := by
        change
          (∫ rho, ‖u (Real.log rho.1)‖ ^ 2
            ∂cc20WindowHaarMeasure lambda hlambda) = _
        rw [htransport]
        apply intervalIntegral.integral_congr
        intro t _ht
        simp only [Real.log_exp]
      _ = ‖cc20GlobalLogWindowContinuousInputToLp lambda hlambda u‖ ^ 2 :=
      (norm_cc20GlobalLogWindowContinuousInputToLp_sq
          lambda hlambda u).symm
  nlinarith [norm_nonneg
      (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
        (cc20WindowLogRestriction lambda hlambda u)),
    norm_nonneg (cc20GlobalLogWindowContinuousInputToLp lambda hlambda u)]

theorem norm_cc20WindowHaarLogL2IsometryEquiv_apply_logRestriction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    ‖cc20WindowHaarLogL2IsometryEquiv lambda hlambda
        (cc20WindowHaarComplexL2Operator lambda hlambda
          (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u)))‖ =
      ‖cc20GlobalLogWindowRegularActionToLp lambda hlambda u‖ := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_cc20WindowHaarComplexL2Operator_logRestriction_eq_global
    lambda hlambda u

theorem norm_cc20GlobalLogWindowRegularActionToLp_le_windowOperatorNorm
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    ‖cc20GlobalLogWindowRegularActionToLp lambda hlambda u‖ ≤
      ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ *
        ‖cc20GlobalLogWindowContinuousInputToLp lambda hlambda u‖ := by
  rw [← norm_cc20WindowHaarComplexL2Operator_logRestriction_eq_global
    lambda hlambda u]
  calc
    ‖cc20WindowHaarComplexL2Operator lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda u))‖ ≤
        ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ *
          ‖ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u)‖ :=
      (cc20WindowHaarComplexL2Operator lambda hlambda).le_opNorm _
    _ = ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ *
        ‖cc20GlobalLogWindowContinuousInputToLp lambda hlambda u‖ := by
      rw [norm_cc20WindowHaarComplex_toLp_logRestriction_eq_global_input]

noncomputable def cc20GlobalLogWindowBoundedContinuousOutputLinearMap
    (lambda : ℝ) (hlambda : 1 < lambda) :
    BoundedContinuousFunction ℝ ℂ →ₗ[ℂ] cc20GlobalLogL2 where
  toFun u :=
    cc20GlobalLogWindowRegularActionToLp lambda hlambda u.toContinuousMap
  map_add' u v := by
    simpa using cc20GlobalLogWindowRegularActionToLp_add
      lambda hlambda u.toContinuousMap v.toContinuousMap
  map_smul' c u := by
    simpa using cc20GlobalLogWindowRegularActionToLp_smul
      lambda hlambda c u.toContinuousMap

theorem norm_cc20GlobalLogWindowContinuousInputToLp_boundedContinuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    ‖cc20GlobalLogWindowContinuousInputToLp
        lambda hlambda u.toContinuousMap‖ =
      ‖BoundedContinuousFunction.toLp 2
        (volume.restrict (cc20LogWindow lambda)) ℂ u‖ := by
  unfold cc20GlobalLogWindowContinuousInputToLp
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (measurableSet_cc20LogWindow lambda)]
  exact congrArg ENNReal.toReal
    (eLpNorm_congr_ae
      (BoundedContinuousFunction.coeFn_toLp 2
        (volume.restrict (cc20LogWindow lambda)) ℂ u).symm)

theorem cc20GlobalLogWindowBoundedContinuousOutputLinearMap_norm_bound
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    ‖cc20GlobalLogWindowBoundedContinuousOutputLinearMap
        lambda hlambda u‖ ≤
      ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ *
        ‖BoundedContinuousFunction.toLp 2
          (volume.restrict (cc20LogWindow lambda)) ℂ u‖ := by
  rw [← norm_cc20GlobalLogWindowContinuousInputToLp_boundedContinuous
    lambda hlambda u]
  exact norm_cc20GlobalLogWindowRegularActionToLp_le_windowOperatorNorm
    lambda hlambda u.toContinuousMap

noncomputable def cc20GlobalLogWindowRestrictedL2Operator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →L[ℂ]
      cc20GlobalLogL2 :=
  LinearMap.extendOfNorm
    (cc20GlobalLogWindowBoundedContinuousOutputLinearMap lambda hlambda)
    (BoundedContinuousFunction.toLp 2
      (volume.restrict (cc20LogWindow lambda)) ℂ).toLinearMap

noncomputable def cc20GlobalLogWindowRestrictedL2Endomorphism
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)).comp
    (cc20GlobalLogWindowRestrictedL2Operator lambda hlambda)

noncomputable def cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((cc20WindowHaarComplexL2Operator lambda hlambda).comp
      (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem cc20WindowHaarRestrictedLogL2IsometryEquiv_intertwines_on_continuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
        (cc20WindowHaarComplexL2Operator lambda hlambda
          (ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u))) =
      LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
        (cc20GlobalLogWindowRegularActionToLp lambda hlambda u) := by
  rw [cc20WindowHaarComplexL2Operator_logRestriction]
  apply (cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda).injective
  change
    cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda
        (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
          (ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda
              (cc20GlobalLogWindowRegularActionContinuous lambda u)))) =
      cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda
        (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
          (cc20GlobalLogWindowRegularActionToLp lambda hlambda u))
  simp only [cc20WindowHaarRestrictedLogL2IsometryEquiv,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change
    Lp.compMeasurePreserving (cc20LogWindowExpPoint lambda hlambda)
        (measurePreserving_cc20LogWindowExpPoint lambda hlambda)
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
          (cc20WindowLogRestriction lambda hlambda
            (cc20GlobalLogWindowRegularActionContinuous lambda u))) =
      Lp.compMeasurePreserving (Subtype.val : CC20LogWindowPoint lambda → ℝ)
        (measurePreserving_cc20LogWindowSubtypeVal lambda)
        (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
          (cc20GlobalLogWindowRegularActionToLp lambda hlambda u))
  rw [Lp.ext_iff]
  let hAction : MemLp
      ((cc20LogWindow lambda).indicator
        (cc20GlobalLogWindowRegularActionContinuous lambda u)) 2 volume :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda u)
  have hleft := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
      (cc20WindowLogRestriction lambda hlambda
        (cc20GlobalLogWindowRegularActionContinuous lambda u)))
    (measurePreserving_cc20LogWindowExpPoint lambda hlambda)
  have hleft_core :=
    (measurePreserving_cc20LogWindowExpPoint lambda hlambda).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (cc20WindowHaarMeasure lambda hlambda) (𝕜 := ℂ)
        (cc20WindowLogRestriction lambda hlambda
          (cc20GlobalLogWindowRegularActionContinuous lambda u)))
  have hright := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
      (cc20GlobalLogWindowRegularActionToLp lambda hlambda u))
    (measurePreserving_cc20LogWindowSubtypeVal lambda)
  have hrestrict :=
    (LpToLpRestrictCLM_coeFn ℂ (cc20LogWindow lambda)
      (cc20GlobalLogWindowRegularActionToLp lambda hlambda u))
  have hglobal := (MemLp.coeFn_toLp hAction).filter_mono
    (ae_restrict_le (μ := volume) (s := cc20LogWindow lambda))
  have hglobal' :
      (cc20GlobalLogWindowRegularActionToLp lambda hlambda u : ℝ → ℂ) =ᵐ[
        volume.restrict (cc20LogWindow lambda)]
        (cc20LogWindow lambda).indicator
          (cc20GlobalLogWindowRegularActionContinuous lambda u) := by
    change
      (hAction.toLp
        ((cc20LogWindow lambda).indicator
          (cc20GlobalLogWindowRegularActionContinuous lambda u)) : ℝ → ℂ) =ᵐ[
        volume.restrict (cc20LogWindow lambda)]
        (cc20LogWindow lambda).indicator
          (cc20GlobalLogWindowRegularActionContinuous lambda u)
    exact hglobal
  have hrestrict_sub :=
    (measurePreserving_cc20LogWindowSubtypeVal lambda).quasiMeasurePreserving.ae_eq_comp
      hrestrict
  have hglobal_sub :=
    (measurePreserving_cc20LogWindowSubtypeVal lambda).quasiMeasurePreserving.ae_eq_comp
      hglobal'
  filter_upwards [hleft, hleft_core, hright, hrestrict_sub, hglobal_sub] with
    t htleft hcore htright hrestrict hglobal
  rw [htleft, hcore, htright, hrestrict, hglobal]
  simp [Function.comp_apply, cc20WindowLogRestriction,
    cc20LogWindowExpPoint, Set.indicator,
    cc20GlobalLogWindowRegularActionContinuous_apply]

theorem cc20GlobalLogWindowRestrictedL2Operator_agrees_on_boundedContinuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    cc20GlobalLogWindowRestrictedL2Operator lambda hlambda
        (BoundedContinuousFunction.toLp 2
          (volume.restrict (cc20LogWindow lambda)) ℂ u) =
      cc20GlobalLogWindowRegularActionToLp
        lambda hlambda u.toContinuousMap := by
  apply LinearMap.extendOfNorm_eq
  · exact BoundedContinuousFunction.toLp_denseRange
      (E := ℂ) (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := volume.restrict (cc20LogWindow lambda)) (by norm_num)
  · exact ⟨‖cc20WindowHaarComplexL2Operator lambda hlambda‖,
      cc20GlobalLogWindowBoundedContinuousOutputLinearMap_norm_bound
        lambda hlambda⟩

theorem cc20GlobalLogWindowRestrictedL2Endomorphism_intertwines_on_boundedContinuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda
        (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
          (ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u.toContinuousMap))) =
      cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
        (cc20WindowHaarComplexL2Operator lambda hlambda
          (ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ
            (cc20WindowLogRestriction lambda hlambda u.toContinuousMap))) := by
  rw [cc20WindowHaarRestrictedLogL2IsometryEquiv_apply_logRestriction]
  rw [cc20WindowHaarRestrictedLogL2IsometryEquiv_intertwines_on_continuous]
  rw [cc20GlobalLogWindowRestrictedL2Endomorphism,
    ContinuousLinearMap.comp_apply,
    cc20GlobalLogWindowRestrictedL2Operator_agrees_on_boundedContinuous]

theorem cc20GlobalLogWindowRestrictedL2Endomorphism_eq_conjugatedHaarOperator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda =
      cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator lambda hlambda := by
  have hdense := BoundedContinuousFunction.toLp_denseRange
    (E := ℂ) (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := volume.restrict (cc20LogWindow lambda)) (by norm_num)
  have heq :
      (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda :
          Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →
            Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) ∘
          BoundedContinuousFunction.toLp 2
            (volume.restrict (cc20LogWindow lambda)) ℂ =
        (cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator lambda hlambda :
          Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →
            Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) ∘
          BoundedContinuousFunction.toLp 2
            (volume.restrict (cc20LogWindow lambda)) ℂ := by
    funext u
    change
      cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda
          (BoundedContinuousFunction.toLp 2
            (volume.restrict (cc20LogWindow lambda)) ℂ u) =
        cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator lambda hlambda
          (BoundedContinuousFunction.toLp 2
            (volume.restrict (cc20LogWindow lambda)) ℂ u)
    rw [← cc20WindowHaarRestrictedLogL2IsometryEquiv_apply_logRestriction
      lambda hlambda u]
    simpa [cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator,
      ContinuousLinearMap.comp_apply] using
      (cc20GlobalLogWindowRestrictedL2Endomorphism_intertwines_on_boundedContinuous
        lambda hlambda u)
  have hfun := hdense.equalizer
    (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda).continuous
    (cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator lambda hlambda).continuous heq
  exact ContinuousLinearMap.ext fun v => congrFun hfun v

theorem isCompactOperator_cc20GlobalLogWindowRestrictedL2Endomorphism
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsCompactOperator
      (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda) := by
  rw [cc20GlobalLogWindowRestrictedL2Endomorphism_eq_conjugatedHaarOperator]
  exact
    (isCompactOperator_cc20WindowHaarComplexL2Operator lambda hlambda).comp_clm
      (cc20WindowHaarRestrictedLogL2IsometryEquiv
        lambda hlambda).symm.toContinuousLinearEquiv.toContinuousLinearMap
    |>.clm_comp
      (cc20WindowHaarRestrictedLogL2IsometryEquiv
        lambda hlambda).toContinuousLinearEquiv.toContinuousLinearMap

theorem cc20GlobalLogWindowRestrictedL2Endomorphism_isSelfAdjoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsSelfAdjoint
      (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda) := by
  rw [cc20GlobalLogWindowRestrictedL2Endomorphism_eq_conjugatedHaarOperator]
  have hSelf :=
    (cc20WindowHaarComplexL2Operator_isSelfAdjoint lambda hlambda).conj_adjoint
      (cc20WindowHaarRestrictedLogL2IsometryEquiv
        lambda hlambda).toContinuousLinearEquiv.toContinuousLinearMap
  simpa only [cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator,
    (cc20WindowHaarRestrictedLogL2IsometryEquiv
      lambda hlambda).adjoint_eq_symm,
    ContinuousLinearMap.comp_assoc] using hSelf

noncomputable def cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))) :
    HilbertBasis ι ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :=
  HilbertBasis.ofRepr
    ((cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).trans
      basis.repr)

theorem cc20GlobalLogWindowRestrictedL2HaarPreimageBasis_apply
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))))
    (i : ι) :
    cc20GlobalLogWindowRestrictedL2HaarPreimageBasis lambda hlambda basis i =
      (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).symm
        (basis i) := by
  classical
  apply (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [cc20GlobalLogWindowRestrictedL2HaarPreimageBasis]
  change
    cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
        ((HilbertBasis.ofRepr
          ((cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).trans
            basis.repr)) i) = basis i
  change
    cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
        ((HilbertBasis.ofRepr
          ((cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).trans
            basis.repr)).repr.symm (lp.single 2 i (1 : ℂ))) = basis i
  have hinv :
      ((cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).trans
        basis.repr).symm =
      basis.repr.symm.trans
        (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).symm := by
    ext x
    rfl
  rw [hinv, LinearIsometryEquiv.trans_apply,
    HilbertBasis.repr_symm_single,
    LinearIsometryEquiv.apply_symm_apply]

theorem cc20GlobalLogWindowRestrictedL2Endomorphism_basis_normSq_summable
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))) :
    Summable (fun i =>
      ‖cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda
        (basis i)‖ ^ 2) := by
  have hH := cc20WindowHaarComplexL2Operator_basis_normSq_summable
    lambda hlambda
      (cc20GlobalLogWindowRestrictedL2HaarPreimageBasis lambda hlambda basis)
  have hnorm (i : ι) :
      ‖cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda
          (basis i)‖ ^ 2 =
        ‖cc20WindowHaarComplexL2Operator lambda hlambda
            (cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
              lambda hlambda basis i)‖ ^ 2 := by
    rw [cc20GlobalLogWindowRestrictedL2Endomorphism_eq_conjugatedHaarOperator]
    rw [cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator]
    change
      ‖(cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda)
          ((cc20WindowHaarComplexL2Operator lambda hlambda)
            ((cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).symm
              (basis i)))‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map,
      cc20GlobalLogWindowRestrictedL2HaarPreimageBasis_apply]
  simpa only [hnorm] using hH

noncomputable def cc20GlobalLogWindowRestrictedL2BasisHilbertSchmidtData
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))) :
    PositiveTrace.BasisHilbertSchmidtData basis where
  operator := cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda
  summable_normSq :=
    cc20GlobalLogWindowRestrictedL2Endomorphism_basis_normSq_summable
      lambda hlambda basis

theorem cc20GlobalLogWindowRestrictedL2PositiveTrace_re_nonnegative
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))) :
    0 ≤ (PositiveTrace.ordinaryTraceAlong basis
      (cc20GlobalLogWindowRestrictedL2BasisHilbertSchmidtData
        lambda hlambda basis).positiveComposition).re :=
  PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
    (cc20GlobalLogWindowRestrictedL2BasisHilbertSchmidtData lambda hlambda basis)

theorem cc20LogWindowProjection_fix_regularActionToLp
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : ContinuousMap ℝ ℂ) :
    cc20LogWindowProjection lambda hlambda
        (cc20GlobalLogWindowRegularActionToLp lambda hlambda u) =
      cc20GlobalLogWindowRegularActionToLp lambda hlambda u := by
  rw [Lp.ext_iff]
  let hAction : MemLp
      ((cc20LogWindow lambda).indicator
        (cc20GlobalLogWindowRegularActionContinuous lambda u)) 2 volume :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
        lambda hlambda u)
  have hAction_coe :
      (cc20GlobalLogWindowRegularActionToLp lambda hlambda u : ℝ → ℂ) =ᵐ[volume]
        (cc20LogWindow lambda).indicator
          (cc20GlobalLogWindowRegularActionContinuous lambda u) := by
    change hAction.toLp
        ((cc20LogWindow lambda).indicator
          (cc20GlobalLogWindowRegularActionContinuous lambda u)) =ᵐ[volume]
      _
    exact MemLp.coeFn_toLp hAction
  filter_upwards
    [cc20LogWindowProjection_coeFn lambda hlambda
        (cc20GlobalLogWindowRegularActionToLp lambda hlambda u),
     hAction_coe] with t hprojection haction
  rw [hprojection]
  by_cases ht : t ∈ cc20LogWindow lambda
  · simp [Set.indicator, ht]
  · have hzero := haction
    rw [Set.indicator_of_notMem ht] at hzero
    simp only [Set.indicator_of_notMem ht]
    exact hzero.symm

theorem cc20GlobalLogWindowRestrictedL2Operator_projection_comp
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (cc20LogWindowProjection lambda hlambda).comp
        (cc20GlobalLogWindowRestrictedL2Operator lambda hlambda) =
      cc20GlobalLogWindowRestrictedL2Operator lambda hlambda := by
  have hdense := BoundedContinuousFunction.toLp_denseRange
    (E := ℂ) (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := volume.restrict (cc20LogWindow lambda)) (by norm_num)
  have hext := LinearMap.extendOfNorm_unique
    hdense ‖cc20WindowHaarComplexL2Operator lambda hlambda‖
    (cc20GlobalLogWindowBoundedContinuousOutputLinearMap_norm_bound
      lambda hlambda)
    ((cc20LogWindowProjection lambda hlambda).comp
      (cc20GlobalLogWindowRestrictedL2Operator lambda hlambda))
    (by
      apply LinearMap.ext
      intro u
      change cc20LogWindowProjection lambda hlambda
          (cc20GlobalLogWindowRestrictedL2Operator lambda hlambda
            (BoundedContinuousFunction.toLp 2
              (volume.restrict (cc20LogWindow lambda)) ℂ u)) =
        cc20GlobalLogWindowBoundedContinuousOutputLinearMap lambda hlambda u
      rw [cc20GlobalLogWindowRestrictedL2Operator_agrees_on_boundedContinuous]
      exact cc20LogWindowProjection_fix_regularActionToLp
        lambda hlambda u.toContinuousMap)
  exact hext.symm

theorem cc20GlobalLogWindowRestrictedL2Operator_eq_zeroExtension_comp
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogWindowRestrictedL2Operator lambda hlambda =
      (cc20LogWindowRestrictIndicatorCLM lambda).comp
        (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda) := by
  rw [cc20GlobalLogWindowRestrictedL2Endomorphism]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [cc20LogWindowRestrictIndicator_comp_restrict lambda hlambda]
  exact (cc20GlobalLogWindowRestrictedL2Operator_projection_comp
    lambda hlambda).symm

theorem norm_cc20GlobalLogWindowRestrictedL2Operator_apply_le
    (lambda : ℝ) (hlambda : 1 < lambda)
    (v : Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) :
    ‖cc20GlobalLogWindowRestrictedL2Operator lambda hlambda v‖ ≤
      ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ * ‖v‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (BoundedContinuousFunction.toLp_denseRange
      (E := ℂ) (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := volume.restrict (cc20LogWindow lambda)) (by norm_num))
    ‖cc20WindowHaarComplexL2Operator lambda hlambda‖
    (cc20GlobalLogWindowBoundedContinuousOutputLinearMap_norm_bound
      lambda hlambda) v

noncomputable def cc20GlobalLogWindowL2Operator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogL2 →L[ℂ] cc20GlobalLogL2 :=
  (cc20GlobalLogWindowRestrictedL2Operator lambda hlambda).comp
    (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda))

theorem cc20GlobalLogWindowContinuousInput_restrict_eq_boundedContinuousToLp
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
        (cc20GlobalLogWindowContinuousInputToLp
          lambda hlambda u.toContinuousMap) =
      BoundedContinuousFunction.toLp 2
        (volume.restrict (cc20LogWindow lambda)) ℂ u := by
  rw [Lp.ext_iff]
  let hInput : MemLp
      ((cc20LogWindow lambda).indicator u.toContinuousMap) 2 volume :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2
      (cc20GlobalLogWindowContinuousInput_memLp_restrict
        lambda hlambda u.toContinuousMap)
  filter_upwards
      [LpToLpRestrictCLM_coeFn ℂ (cc20LogWindow lambda)
        (cc20GlobalLogWindowContinuousInputToLp
          lambda hlambda u.toContinuousMap),
       (MemLp.coeFn_toLp hInput).filter_mono ae_restrict_le,
       BoundedContinuousFunction.coeFn_toLp 2
        (volume.restrict (cc20LogWindow lambda)) ℂ u,
       ae_restrict_mem (measurableSet_cc20LogWindow lambda)] with
      t hrestrict hglobal hbounded ht
  rw [hrestrict, hbounded]
  change cc20GlobalLogWindowContinuousInputToLp
      lambda hlambda u.toContinuousMap t = u t
  rw [show cc20GlobalLogWindowContinuousInputToLp
      lambda hlambda u.toContinuousMap =
      hInput.toLp ((cc20LogWindow lambda).indicator u.toContinuousMap) by rfl]
  rw [hglobal]
  exact Set.indicator_of_mem ht _

theorem cc20GlobalLogWindowL2Operator_agrees_on_boundedContinuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : BoundedContinuousFunction ℝ ℂ) :
    cc20GlobalLogWindowL2Operator lambda hlambda
        (cc20GlobalLogWindowContinuousInputToLp
          lambda hlambda u.toContinuousMap) =
      cc20GlobalLogWindowRegularActionToLp
        lambda hlambda u.toContinuousMap := by
  rw [cc20GlobalLogWindowL2Operator,
    ContinuousLinearMap.comp_apply,
    cc20GlobalLogWindowContinuousInput_restrict_eq_boundedContinuousToLp,
    cc20GlobalLogWindowRestrictedL2Operator_agrees_on_boundedContinuous]

theorem cc20LogWindowProjection_restrict_eq
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2) :
    LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
        (cc20LogWindowProjection lambda hlambda u) =
      LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda) u := by
  rw [Lp.ext_iff]
  filter_upwards
    [LpToLpRestrictCLM_coeFn ℂ (cc20LogWindow lambda)
        (cc20LogWindowProjection lambda hlambda u),
     LpToLpRestrictCLM_coeFn ℂ (cc20LogWindow lambda) u,
     (cc20LogWindowProjection_coeFn lambda hlambda u).filter_mono
       ae_restrict_le,
     ae_restrict_mem (measurableSet_cc20LogWindow lambda)] with
      t hprojected hinput hindicator ht
  rw [hprojected, hinput, hindicator]
  exact Set.indicator_of_mem ht _

theorem cc20GlobalLogWindowL2Operator_comp_projection
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (cc20GlobalLogWindowL2Operator lambda hlambda).comp
        (cc20LogWindowProjection lambda hlambda) =
      cc20GlobalLogWindowL2Operator lambda hlambda := by
  apply ContinuousLinearMap.ext
  intro u
  change cc20GlobalLogWindowRestrictedL2Operator lambda hlambda
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda)
        (cc20LogWindowProjection lambda hlambda u)) =
    cc20GlobalLogWindowRestrictedL2Operator lambda hlambda
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (cc20LogWindow lambda) u)
  rw [cc20LogWindowProjection_restrict_eq]

theorem cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogWindowL2Operator lambda hlambda =
      ((cc20LogWindowRestrictIndicatorCLM lambda).comp
        (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda)).comp
          (cc20LogWindowRestrictIndicatorCLM lambda).adjoint := by
  rw [cc20GlobalLogWindowL2Operator,
    cc20GlobalLogWindowRestrictedL2Operator_eq_zeroExtension_comp]
  rw [cc20LogWindowRestrict_eq_adjoint_restrictIndicatorCLM]

theorem isCompactOperator_cc20GlobalLogWindowL2Operator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsCompactOperator (cc20GlobalLogWindowL2Operator lambda hlambda) := by
  rw [cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation]
  exact
    (isCompactOperator_cc20GlobalLogWindowRestrictedL2Endomorphism
      lambda hlambda).clm_comp
        (cc20LogWindowRestrictIndicatorCLM lambda)
    |>.comp_clm (cc20LogWindowRestrictIndicatorCLM lambda).adjoint

theorem cc20GlobalLogWindowL2Operator_isSelfAdjoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsSelfAdjoint (cc20GlobalLogWindowL2Operator lambda hlambda) := by
  rw [cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation]
  exact
    (cc20GlobalLogWindowRestrictedL2Endomorphism_isSelfAdjoint
      lambda hlambda).conj_adjoint
        (cc20LogWindowRestrictIndicatorCLM lambda)

theorem norm_cc20GlobalLogWindowL2Operator_apply_le
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2) :
    ‖cc20GlobalLogWindowL2Operator lambda hlambda u‖ ≤
      ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ * ‖u‖ := by
  calc
    ‖cc20GlobalLogWindowL2Operator lambda hlambda u‖ =
        ‖cc20GlobalLogWindowRestrictedL2Operator lambda hlambda
          (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
            (cc20LogWindow lambda) u)‖ := rfl
    _ ≤ ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ *
        ‖LpToLpRestrictCLM ℝ ℂ ℂ volume 2
          (cc20LogWindow lambda) u‖ :=
      norm_cc20GlobalLogWindowRestrictedL2Operator_apply_le
        lambda hlambda _
    _ ≤ ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ * ‖u‖ :=
      mul_le_mul_of_nonneg_left
        (norm_Lp_toLp_restrict_le (cc20LogWindow lambda) u)
        (norm_nonneg _)

theorem cc20GlobalLogWindowContinuousInputToLp_eq_logPullbackLp
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (hsupport : Function.support (cc20LogPullback p) ⊆
      cc20LogWindow lambda) :
    cc20GlobalLogWindowContinuousInputToLp lambda hlambda
        (ofCompactSupport
          (cc20LogPullback p) (continuous_cc20LogPullback p)
          (hasCompactSupport_cc20LogPullback p)).toContinuousMap =
      cc20LogPullbackLp p := by
  let u : BoundedContinuousFunction ℝ ℂ :=
    ofCompactSupport
      (cc20LogPullback p) (continuous_cc20LogPullback p)
      (hasCompactSupport_cc20LogPullback p)
  have hu_memLp : MemLp (cc20LogPullback p) 2
      (volume.restrict (cc20LogWindow lambda)) := by
    simpa [u] using
      (cc20GlobalLogWindowContinuousInput_memLp_restrict
        lambda hlambda u.toContinuousMap)
  let hInput : MemLp
      ((cc20LogWindow lambda).indicator (cc20LogPullback p)) 2 volume :=
    (memLp_indicator_iff_restrict
      (measurableSet_cc20LogWindow lambda)).2 hu_memLp
  apply MemLp.toLp_congr hInput (cc20LogPullback_memLp p)
  filter_upwards
    [cc20LogPullbackLp_coeFn p] with t hpull
  by_cases ht : t ∈ cc20LogWindow lambda
  · simp only [Set.indicator_of_mem ht]
  · have hzero : cc20LogPullback p t = 0 := by
      by_contra hne
      exact ht (hsupport (by simpa [Function.mem_support] using hne))
    simp [Set.indicator, ht, hzero, hpull]

theorem cc20GlobalLogWindowL2Operator_eq_on_logPullback_of_le
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (lambda mu : ℝ) (hlambda : 1 < lambda) (hmu : 1 < mu)
    (hle : lambda ≤ mu)
    (hsupport : Function.support (cc20LogPullback p) ⊆
      cc20LogWindow lambda) :
    cc20LogWindowProjection lambda hlambda
        (cc20GlobalLogWindowL2Operator mu hmu (cc20LogPullbackLp p)) =
      cc20GlobalLogWindowL2Operator lambda hlambda (cc20LogPullbackLp p) := by
  let u : BoundedContinuousFunction ℝ ℂ :=
    ofCompactSupport
      (cc20LogPullback p) (continuous_cc20LogPullback p)
      (hasCompactSupport_cc20LogPullback p)
  calc
    cc20LogWindowProjection lambda hlambda
        (cc20GlobalLogWindowL2Operator mu hmu (cc20LogPullbackLp p)) =
      cc20LogWindowProjection lambda hlambda
        (cc20GlobalLogWindowL2Operator mu hmu
          (cc20GlobalLogWindowContinuousInputToLp mu hmu u.toContinuousMap)) := by
      rw [cc20GlobalLogWindowContinuousInputToLp_eq_logPullbackLp
        p mu hmu (fun t ht =>
          cc20LogWindow_subset_of_le lambda mu hlambda hmu hle (hsupport ht))]
    _ = cc20LogWindowProjection lambda hlambda
          (cc20GlobalLogWindowRegularActionToLp mu hmu u.toContinuousMap) := by
      rw [cc20GlobalLogWindowL2Operator_agrees_on_boundedContinuous]
    _ = cc20GlobalLogWindowRegularActionToLp lambda hlambda u.toContinuousMap := by
      let hmuAction :=
        (memLp_indicator_iff_restrict
          (measurableSet_cc20LogWindow mu)).2
          (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
            mu hmu u.toContinuousMap)
      let hlambdaAction :=
        (memLp_indicator_iff_restrict
          (measurableSet_cc20LogWindow lambda)).2
          (cc20GlobalLogWindowRegularActionContinuous_memLp_restrict
            lambda hlambda u.toContinuousMap)
      have hmuAction_coe :
          (cc20GlobalLogWindowRegularActionToLp mu hmu u.toContinuousMap : ℝ → ℂ) =ᵐ[volume]
            (cc20LogWindow mu).indicator
              (cc20GlobalLogWindowRegularActionContinuous mu u.toContinuousMap) := by
        change hmuAction.toLp
            ((cc20LogWindow mu).indicator
              (cc20GlobalLogWindowRegularActionContinuous mu u.toContinuousMap)) =ᵐ[volume]
          _
        exact MemLp.coeFn_toLp hmuAction
      have hlambdaAction_coe :
          (cc20GlobalLogWindowRegularActionToLp lambda hlambda u.toContinuousMap : ℝ → ℂ) =ᵐ[volume]
            (cc20LogWindow lambda).indicator
              (cc20GlobalLogWindowRegularActionContinuous lambda u.toContinuousMap) := by
        change hlambdaAction.toLp
            ((cc20LogWindow lambda).indicator
              (cc20GlobalLogWindowRegularActionContinuous lambda u.toContinuousMap)) =ᵐ[volume]
          _
        exact MemLp.coeFn_toLp hlambdaAction
      rw [Lp.ext_iff]
      filter_upwards
        [cc20LogWindowProjection_coeFn lambda hlambda
            (cc20GlobalLogWindowRegularActionToLp mu hmu u.toContinuousMap),
         hmuAction_coe, hlambdaAction_coe] with
        t hprojection hmuFn hlambdaFn
      by_cases ht : t ∈ cc20LogWindow lambda
      · rw [hprojection]
        simp only [Set.indicator_of_mem ht]
        rw [hmuFn, hlambdaFn]
        have hsubset := cc20LogWindow_subset_of_le
          lambda mu hlambda hmu hle
        simp only [Set.indicator_of_mem (hsubset ht),
          Set.indicator_of_mem ht]
        simpa only [cc20GlobalLogWindowRegularActionContinuous_apply] using
          (cc20GlobalLogWindowRegularAction_eq_of_support_subset
            lambda mu hlambda hmu hle t u.toContinuousMap hsupport)
      · rw [hprojection]
        simp only [Set.indicator_of_notMem ht]
        exact (hlambdaFn.trans (Set.indicator_of_notMem ht _)).symm
    _ = cc20GlobalLogWindowL2Operator lambda hlambda
          (cc20GlobalLogWindowContinuousInputToLp lambda hlambda u.toContinuousMap) :=
      (cc20GlobalLogWindowL2Operator_agrees_on_boundedContinuous
        lambda hlambda u).symm
    _ = cc20GlobalLogWindowL2Operator lambda hlambda (cc20LogPullbackLp p) := by
      rw [cc20GlobalLogWindowContinuousInputToLp_eq_logPullbackLp
        p lambda hlambda hsupport]

theorem exists_cc20GlobalLogWindowL2Operator_source_compatibility
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ∃ (lambda : ℝ) (hlambda : 1 < lambda),
      ∀ (mu : ℝ) (hmu : 1 < mu), lambda ≤ mu →
        cc20LogWindowProjection lambda hlambda
            (cc20GlobalLogWindowL2Operator mu hmu
              (cc20LogPullbackLp p)) =
          cc20GlobalLogWindowL2Operator lambda hlambda
            (cc20LogPullbackLp p) := by
  obtain ⟨lambda, hlambda, hsupport⟩ :=
    exists_cc20LogWindow_containing_logPullback p
  refine ⟨lambda, hlambda, ?_⟩
  intro mu hmu hle
  exact cc20GlobalLogWindowL2Operator_eq_on_logPullback_of_le
    p lambda mu hlambda hmu hle hsupport

theorem exists_cc20LogWindow_containing_finite_logPullbacks
    (s : Finset
      CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ∃ (lambda : ℝ) (hlambda : 1 < lambda),
      ∀ p ∈ s, Function.support (cc20LogPullback p) ⊆ cc20LogWindow lambda := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨2, by norm_num, ?_⟩
      intro p hp
      simp at hp
  | @insert p s hp ih =>
      obtain ⟨lambdaP, hlambdaP, hsupportP⟩ :=
        exists_cc20LogWindow_containing_logPullback p
      obtain ⟨lambdaS, hlambdaS, hsupportS⟩ := ih
      let lambda := max lambdaP lambdaS
      have hlambda : 1 < lambda :=
        lt_of_lt_of_le hlambdaP (le_max_left _ _)
      refine ⟨lambda, hlambda, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hsupportP.trans (cc20LogWindow_subset_of_le lambdaP lambda
          hlambdaP hlambda (le_max_left _ _))
      · exact (hsupportS q hq).trans (cc20LogWindow_subset_of_le lambdaS lambda
          hlambdaS hlambda (le_max_right _ _))

theorem cc20GlobalLogWindowL2Operator_eq_on_finite_logPullback_sum_of_le
    (s : Finset
      CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (c : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest → ℂ)
    (lambda mu : ℝ) (hlambda : 1 < lambda) (hmu : 1 < mu)
    (hle : lambda ≤ mu)
    (hsupport : ∀ p ∈ s, Function.support (cc20LogPullback p) ⊆
      cc20LogWindow lambda) :
    cc20LogWindowProjection lambda hlambda
        (cc20GlobalLogWindowL2Operator mu hmu
          (s.sum fun p => c p • cc20LogPullbackLp p)) =
      cc20GlobalLogWindowL2Operator lambda hlambda
        (s.sum fun p => c p • cc20LogPullbackLp p) := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simpa only [map_smul] using congrArg (fun v => c p • v)
    (cc20GlobalLogWindowL2Operator_eq_on_logPullback_of_le
      p lambda mu hlambda hmu hle (hsupport p hp))

end CC20Concrete
end Source
end ConnesWeilRH
