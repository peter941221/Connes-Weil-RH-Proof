/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Integrability of the selected archimedean density

The proof first removes the right-hand singularity at zero and then controls
the exponential tail outside the compact support of the convolution square.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedWeilSquare
namespace SelectedWeilSquareOwner

open Filter MeasureTheory Set
open scoped ContDiff Filter Topology

noncomputable def archimedeanNumeratorRe
    (owner : SelectedWeilSquareOwner) (y : ℝ) : ℝ :=
  (owner.archimedeanNumerator y).re

noncomputable def archimedeanNumeratorIm
    (owner : SelectedWeilSquareOwner) (y : ℝ) : ℝ :=
  (owner.archimedeanNumerator y).im

theorem archimedeanNumeratorRe_contDiff
    (owner : SelectedWeilSquareOwner) :
    ContDiff ℝ ∞ owner.archimedeanNumeratorRe := by
  exact Complex.reCLM.contDiff.comp owner.archimedeanNumerator_contDiff

theorem archimedeanNumeratorIm_contDiff
    (owner : SelectedWeilSquareOwner) :
    ContDiff ℝ ∞ owner.archimedeanNumeratorIm := by
  exact Complex.imCLM.contDiff.comp owner.archimedeanNumerator_contDiff

@[simp] theorem archimedeanNumeratorRe_zero
    (owner : SelectedWeilSquareOwner) :
    owner.archimedeanNumeratorRe 0 = 0 := by
  simp [archimedeanNumeratorRe]

@[simp] theorem archimedeanNumeratorIm_zero
    (owner : SelectedWeilSquareOwner) :
    owner.archimedeanNumeratorIm 0 = 0 := by
  simp [archimedeanNumeratorIm]

theorem hasDerivAt_archimedeanDenominator (y : ℝ) :
    HasDerivAt archimedeanDenominator
      (Real.exp y + Real.exp (-y)) y := by
  have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x))
      (-Real.exp (-y)) y := by
    simpa only [mul_neg, mul_one] using
      ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))
  simpa [archimedeanDenominator, sub_neg_eq_add] using
    (Real.hasDerivAt_exp y).sub hneg

theorem archimedeanDenominator_deriv_ne_zero (y : ℝ) :
    Real.exp y + Real.exp (-y) ≠ 0 := by
  positivity

theorem archimedeanDenominator_pos {y : ℝ} (hy : 0 < y) :
    0 < archimedeanDenominator y := by
  rw [archimedeanDenominator, sub_pos]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem archimedeanIntegrand_continuousOn_Ioi
    (owner : SelectedWeilSquareOwner) :
    ContinuousOn owner.archimedeanIntegrand (Ioi (0 : ℝ)) := by
  intro y hy
  have hnum : ContinuousAt owner.archimedeanNumerator y :=
    owner.archimedeanNumerator_contDiff.continuous.continuousAt
  have hden : ContinuousAt (fun x : ℝ => (archimedeanDenominator x : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp
      archimedeanDenominator_contDiff.continuous.continuousAt
  apply ContinuousAt.continuousWithinAt
  exact hnum.div hden (by exact_mod_cast (archimedeanDenominator_pos hy).ne')

theorem tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT
    (owner : SelectedWeilSquareOwner) :
    Tendsto
      (fun y => owner.archimedeanNumeratorRe y / archimedeanDenominator y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deriv owner.archimedeanNumeratorRe 0 / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := deriv owner.archimedeanNumeratorRe)
      (g' := fun y => Real.exp y + Real.exp (-y))
  · exact Filter.Eventually.of_forall fun y =>
      ((owner.archimedeanNumeratorRe_contDiff.differentiable (by simp)) y).hasDerivAt
  · exact Filter.Eventually.of_forall hasDerivAt_archimedeanDenominator
  · exact Filter.Eventually.of_forall archimedeanDenominator_deriv_ne_zero
  · simpa using
      Filter.Tendsto.mono_left
        owner.archimedeanNumeratorRe_contDiff.continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · simpa using
      Filter.Tendsto.mono_left
        archimedeanDenominator_contDiff.continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · have hnum :=
      owner.archimedeanNumeratorRe_contDiff.continuous_deriv (by simp)
    have hden : Continuous (fun y : ℝ => Real.exp y + Real.exp (-y)) := by
      fun_prop
    simpa only [Pi.div_apply, Real.exp_zero, neg_zero, add_zero, one_add_one_eq_two] using
      ((hnum.tendsto 0).div (hden.tendsto 0) (by norm_num)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

theorem tendsto_archimedeanNumeratorIm_div_denominator_nhdsGT
    (owner : SelectedWeilSquareOwner) :
    Tendsto
      (fun y => owner.archimedeanNumeratorIm y / archimedeanDenominator y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deriv owner.archimedeanNumeratorIm 0 / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := deriv owner.archimedeanNumeratorIm)
      (g' := fun y => Real.exp y + Real.exp (-y))
  · exact Filter.Eventually.of_forall fun y =>
      ((owner.archimedeanNumeratorIm_contDiff.differentiable (by simp)) y).hasDerivAt
  · exact Filter.Eventually.of_forall hasDerivAt_archimedeanDenominator
  · exact Filter.Eventually.of_forall archimedeanDenominator_deriv_ne_zero
  · simpa using
      Filter.Tendsto.mono_left
        owner.archimedeanNumeratorIm_contDiff.continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · simpa using
      Filter.Tendsto.mono_left
        archimedeanDenominator_contDiff.continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · have hnum :=
      owner.archimedeanNumeratorIm_contDiff.continuous_deriv (by simp)
    have hden : Continuous (fun y : ℝ => Real.exp y + Real.exp (-y)) := by
      fun_prop
    simpa only [Pi.div_apply, Real.exp_zero, neg_zero, add_zero, one_add_one_eq_two] using
      ((hnum.tendsto 0).div (hden.tendsto 0) (by norm_num)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

noncomputable def archimedeanIntegrandLimit
    (owner : SelectedWeilSquareOwner) : ℂ :=
  (deriv owner.archimedeanNumeratorRe 0 / 2 : ℂ) +
    (deriv owner.archimedeanNumeratorIm 0 / 2 : ℂ) * Complex.I

theorem tendsto_archimedeanIntegrand_nhdsGT
    (owner : SelectedWeilSquareOwner) :
    Tendsto owner.archimedeanIntegrand (𝓝[>] (0 : ℝ))
      (𝓝 owner.archimedeanIntegrandLimit) := by
  have hre := owner.tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT
  have him := owner.tendsto_archimedeanNumeratorIm_div_denominator_nhdsGT
  have hre' := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have him' := Complex.continuous_ofReal.continuousAt.tendsto.comp him
  have hsum := hre'.add (him'.mul_const Complex.I)
  convert hsum using 1
  · funext y
    apply Complex.ext <;>
      simp [archimedeanIntegrand, archimedeanNumeratorRe,
        archimedeanNumeratorIm]
  · simp [archimedeanIntegrandLimit]

noncomputable def archimedeanTailRatio (y : ℝ) : ℝ :=
  Real.exp y / archimedeanDenominator y

theorem tendsto_archimedeanTailRatio_atTop :
    Tendsto archimedeanTailRatio atTop (𝓝 1) := by
  have hlinear : Tendsto (fun y : ℝ => (-2 : ℝ) * y) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by norm_num)).2 tendsto_id
  have hexp : Tendsto (fun y : ℝ => Real.exp ((-2 : ℝ) * y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlinear
  have hinv : Tendsto (fun y : ℝ => (1 - Real.exp ((-2 : ℝ) * y))⁻¹)
      atTop (𝓝 1) := by
    have hsub : Tendsto (fun y : ℝ => 1 - Real.exp ((-2 : ℝ) * y))
        atTop (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub hexp
    simpa using hsub.inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hfactor :
      archimedeanDenominator y =
        Real.exp y * (1 - Real.exp ((-2 : ℝ) * y)) := by
    rw [archimedeanDenominator, mul_sub, mul_one, ← Real.exp_add]
    rw [show y + -2 * y = -y by ring]
  have hright : 1 - Real.exp ((-2 : ℝ) * y) ≠ 0 := by
    have : Real.exp ((-2 : ℝ) * y) < 1 := by
      exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by norm_num) hy)
    exact sub_ne_zero.mpr (ne_of_gt this)
  rw [archimedeanTailRatio, hfactor]
  field_simp [Real.exp_ne_zero, hright]

theorem eventually_archimedeanIntegrand_eq_tail
    (owner : SelectedWeilSquareOwner) :
    ∀ᶠ y in atTop,
      owner.archimedeanIntegrand y =
        (-2 * owner.convolutionSquare.test 0) *
          (Real.exp (-y) : ℂ) * (archimedeanTailRatio y : ℂ) := by
  filter_upwards [eventually_gt_atTop (max 1 owner.supportRadius)] with y hy
  have hy0 : 0 < y :=
    (lt_of_lt_of_le (by norm_num) (le_max_left 1 owner.supportRadius)).trans hy
  have hyradius : owner.supportRadius < |y| := by
    simpa [abs_of_pos hy0] using lt_of_le_of_lt (le_max_right 1 owner.supportRadius) hy
  have hyzero := owner.convolutionSquare_eq_zero_of_abs_gt y hyradius
  have hnegzero := owner.convolutionSquare_eq_zero_of_abs_gt (-y) (by simpa using hyradius)
  have hden : archimedeanDenominator y ≠ 0 :=
    (archimedeanDenominator_pos hy0).ne'
  have hexp : Real.exp y ≠ 0 := Real.exp_ne_zero y
  simp only [archimedeanIntegrand, archimedeanNumerator, hyzero, hnegzero,
    add_zero, mul_zero, zero_sub]
  rw [archimedeanTailRatio]
  push_cast
  field_simp [hden, hexp, Real.exp_neg]
  have hcexp : Complex.exp (-(y : ℂ)) * Complex.exp (y : ℂ) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [mul_assoc, hcexp, mul_one]

theorem archimedeanIntegrand_isBigO_exp_neg
    (owner : SelectedWeilSquareOwner) :
    owner.archimedeanIntegrand =O[atTop]
      (fun y : ℝ => (Real.exp (-y) : ℂ)) := by
  have hratio_lt : ∀ᶠ y in atTop, archimedeanTailRatio y < 2 :=
    (tendsto_order.1 tendsto_archimedeanTailRatio_atTop).2 2 (by norm_num)
  have hratio_nonneg : ∀ᶠ y in atTop, 0 ≤ archimedeanTailRatio y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact div_nonneg (Real.exp_pos y).le (archimedeanDenominator_pos hy).le
  apply Asymptotics.IsBigO.of_bound
      (2 * ‖(-2 : ℂ) * owner.convolutionSquare.test 0‖)
  filter_upwards [owner.eventually_archimedeanIntegrand_eq_tail,
    hratio_lt, hratio_nonneg] with y heq hlt hnonneg
  rw [heq, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-y))]
  have hratio_abs : |archimedeanTailRatio y| ≤ 2 := by
    simpa [abs_of_nonneg hnonneg] using hlt.le
  calc
    ‖(-2 : ℂ) * owner.convolutionSquare.test 0‖ * Real.exp (-y) *
          |archimedeanTailRatio y|
        ≤ ‖(-2 : ℂ) * owner.convolutionSquare.test 0‖ * Real.exp (-y) * 2 :=
      mul_le_mul_of_nonneg_left hratio_abs
        (mul_nonneg (norm_nonneg _) (Real.exp_pos (-y)).le)
    _ = (2 * ‖(-2 : ℂ) * owner.convolutionSquare.test 0‖) *
          Real.exp (-y) := by ring

theorem archimedeanIntegrand_integrableOn_Ioi
    (owner : SelectedWeilSquareOwner) :
    IntegrableOn owner.archimedeanIntegrand (Ioi (0 : ℝ)) := by
  rw [integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin]
  refine ⟨?_, ?_, owner.archimedeanIntegrand_continuousOn_Ioi.locallyIntegrableOn
    measurableSet_Ioi⟩
  · have hexpReal : IntegrableOn (fun y : ℝ => Real.exp (-1 * y)) (Ioi (0 : ℝ)) :=
      exp_neg_integrableOn_Ioi 0 (by norm_num)
    have hexpComplex : IntegrableOn (fun y : ℝ => (Real.exp (-y) : ℂ))
        (Ioi (0 : ℝ)) := by
      simpa [Function.comp_def] using Complex.ofRealCLM.integrableOn_comp hexpReal
    have hexpFilter : IntegrableAtFilter (fun y : ℝ => (Real.exp (-y) : ℂ))
        atTop :=
      ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0, hexpComplex⟩
    have hmeas : StronglyMeasurableAtFilter owner.archimedeanIntegrand atTop :=
      ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0,
        owner.archimedeanIntegrand_continuousOn_Ioi.aestronglyMeasurable
          measurableSet_Ioi⟩
    exact owner.archimedeanIntegrand_isBigO_exp_neg.integrableAtFilter hmeas hexpFilter
  · have hmeas : StronglyMeasurableAtFilter owner.archimedeanIntegrand (𝓝[>] (0 : ℝ)) :=
      owner.archimedeanIntegrand_continuousOn_Ioi
        |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0
    exact owner.tendsto_archimedeanIntegrand_nhdsGT.integrableAtFilter hmeas
      (volume.finiteAt_nhdsWithin 0 (Ioi (0 : ℝ)))

noncomputable def selectedArchimedeanData
    (owner : SelectedWeilSquareOwner) :
    SelectedWeilFormula.SelectedArchimedeanData owner where
  integrable := owner.archimedeanIntegrand_integrableOn_Ioi

end SelectedWeilSquareOwner
end SelectedWeilSquare

namespace SelectedWeilFormula
namespace SelectedWeilFormulaOwner

/-- The selected formula owner has no external analytic premise. -/
noncomputable def ofSquare
    (square : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SelectedWeilFormulaOwner where
  square := square
  finiteSupport := SelectedWeilSquare.SelectedFinitePrimeSupportData.ofOwner square
  archimedean := square.selectedArchimedeanData

/-- Construct the complete selected formula owner from one compact log test. -/
noncomputable def ofCompactLogTest
    (sourceTest : CompactLogConvolution.CompactLogTest) :
    SelectedWeilFormulaOwner :=
  ofSquare (SelectedWeilSquare.SelectedWeilSquareOwner.ofCompactLogTest sourceTest)

end SelectedWeilFormulaOwner
end SelectedWeilFormula
end CCM25Concrete
end Source
end ConnesWeilRH
