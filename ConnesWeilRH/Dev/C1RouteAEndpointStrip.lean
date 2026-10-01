import ConnesWeilRH.Dev.C1RouteAOwnerTest
import ConnesWeilRH.Dev.C1RouteAStripTransfer
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace ConnesWeilRH.Dev

open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open scoped ContDiff

theorem expWeightedIntegral_le_of_endpoint_bounds {g : ℝ → ℝ}
    (hg : Continuous g) (hgnn : ∀ position, 0 ≤ g position)
    {radius upper sigma : ℝ}
    (hsupp : Function.support g ⊆ Set.Icc (-radius) radius)
    (hsigma : sigma ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    (hlower : (∫ position : ℝ, Real.exp (-(1 / 2) * position) * g position) ≤ upper)
    (hupper : (∫ position : ℝ, Real.exp ((1 / 2) * position) * g position) ≤ upper) :
    (∫ position : ℝ, Real.exp (sigma * position) * g position) ≤ upper := by
  have hleft : 0 ≤ 1 / 2 - sigma := by linarith [hsigma.2]
  have hright : 0 ≤ sigma + 1 / 2 := by linarith [hsigma.1]
  have hint (exponent : ℝ) :
      Integrable (fun position : ℝ => Real.exp (exponent * position) * g position) := by
    have hcont : Continuous (fun position : ℝ => Real.exp (exponent * position) * g position) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hg
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-radius) radius) isCompact_Icc ?_
    intro position hposition
    exact hsupp (mul_ne_zero_iff.mp hposition).2
  have hpoint (position : ℝ) :
      Real.exp (sigma * position) * g position ≤
        (1 / 2 - sigma) * (Real.exp (-(1 / 2) * position) * g position) +
        (sigma + 1 / 2) * (Real.exp ((1 / 2) * position) * g position) := by
    have hconvex := convexOn_exp.2
      (Set.mem_univ (-(1 / 2) * position)) (Set.mem_univ ((1 / 2) * position))
      hleft hright (by ring : (1 / 2 - sigma) + (sigma + 1 / 2) = 1)
    simp only [smul_eq_mul] at hconvex
    have hargument :
        (1 / 2 - sigma) * (-(1 / 2) * position) +
          (sigma + 1 / 2) * ((1 / 2) * position) = sigma * position := by ring
    rw [hargument] at hconvex
    calc Real.exp (sigma * position) * g position
        ≤ ((1 / 2 - sigma) * Real.exp (-(1 / 2) * position) +
          (sigma + 1 / 2) * Real.exp ((1 / 2) * position)) * g position :=
            mul_le_mul_of_nonneg_right hconvex (hgnn position)
      _ = _ := by ring
  calc (∫ position : ℝ, Real.exp (sigma * position) * g position)
      ≤ ∫ position : ℝ,
        (1 / 2 - sigma) * (Real.exp (-(1 / 2) * position) * g position) +
        (sigma + 1 / 2) * (Real.exp ((1 / 2) * position) * g position) := by
          apply integral_mono_of_nonneg
          · filter_upwards with position
            exact mul_nonneg (Real.exp_nonneg _) (hgnn position)
          · exact ((hint (-(1 / 2))).const_mul _).add ((hint (1 / 2)).const_mul _)
          · filter_upwards with position
            exact hpoint position
    _ = (1 / 2 - sigma) * (∫ position : ℝ, Real.exp (-(1 / 2) * position) * g position) +
        (sigma + 1 / 2) * (∫ position : ℝ, Real.exp ((1 / 2) * position) * g position) := by
          rw [integral_add ((hint (-(1 / 2))).const_mul _) ((hint (1 / 2)).const_mul _),
            integral_const_mul, integral_const_mul]
    _ ≤ (1 / 2 - sigma) * upper + (sigma + 1 / 2) * upper :=
      add_le_add (mul_le_mul_of_nonneg_left hlower hleft)
        (mul_le_mul_of_nonneg_left hupper hright)
    _ = upper := by ring

theorem stripNorm_le_of_endpoint_bounds (function : ℝ → ℂ)
    (hfunction : Continuous function) {radius upper sigma : ℝ}
    (hsupp : Function.support function ⊆ Set.Icc (-radius) radius)
    (hsigma : sigma ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    (hlower : stripNorm (-(1 / 2)) function ≤ upper)
    (hupper : stripNorm (1 / 2) function ≤ upper) :
    stripNorm sigma function ≤ upper := by
  exact expWeightedIntegral_le_of_endpoint_bounds hfunction.norm
    (fun position => norm_nonneg (function position))
    (fun position hposition => hsupp fun hzero => hposition (by simp [hzero]))
    hsigma hlower hupper

theorem stripSecondNorm_le_of_endpoint_bounds (function : ℝ → ℂ)
    (hfunction : Continuous (deriv (deriv function))) {radius upper sigma : ℝ}
    (hsupp : Function.support (deriv (deriv function)) ⊆ Set.Icc (-radius) radius)
    (hsigma : sigma ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    (hlower : stripSecondNorm (-(1 / 2)) function ≤ upper)
    (hupper : stripSecondNorm (1 / 2) function ≤ upper) :
    stripSecondNorm sigma function ≤ upper := by
  exact stripNorm_le_of_endpoint_bounds (deriv (deriv function)) hfunction
    hsupp hsigma hlower hupper

def baseNormUpper2343 : ℝ := 2.7790943782
def baseSecondUpper2343 : ℝ := 9044.9434472
def correctionNormUpper2343 : ℝ := 231.2642026141
def correctionSecondUpper2343 : ℝ := 666472.585392

theorem endpoint_min_product_le_frozen :
    min (baseSecondUpper2343 * correctionNormUpper2343)
        (correctionSecondUpper2343 * baseNormUpper2343) ≤ bUpper2243 := by
  norm_num [baseNormUpper2343, baseSecondUpper2343,
    correctionNormUpper2343, correctionSecondUpper2343, bUpper2243]

theorem frozenStripHypothesis_of_compact_endpoint_bounds (base correction : CompactLogTest)
    {radius : ℝ}
    (hsuppBase : tsupport (base.test : ℝ → ℂ) ⊆ Set.Icc (-radius) radius)
    (hsuppCorrection : tsupport (correction.test : ℝ → ℂ) ⊆ Set.Icc (-radius) radius)
    (hbase : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (base.test : ℝ → ℂ) ≤ baseNormUpper2343)
    (hbaseSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (base.test : ℝ → ℂ) ≤ baseSecondUpper2343)
    (hcorrection : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (correction.test : ℝ → ℂ) ≤ correctionNormUpper2343)
    (hcorrectionSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (correction.test : ℝ → ℂ) ≤ correctionSecondUpper2343) :
    FrozenStripHypothesis base correction := by
  have hb2 : Continuous (deriv (deriv (base.test : ℝ → ℂ))) :=
    (ContDiff.deriv'
      ((base.test.smooth ⊤).of_le (by decide : (2 : ℕ∞ω) ≤ ∞))).continuous_deriv
      (by decide : (1 : ℕ∞ω) ≤ 1)
  have hc2 : Continuous (deriv (deriv (correction.test : ℝ → ℂ))) :=
    (ContDiff.deriv'
      ((correction.test.smooth ⊤).of_le (by decide : (2 : ℕ∞ω) ≤ ∞))).continuous_deriv
      (by decide : (1 : ℕ∞ω) ≤ 1)
  have hbs := (subset_tsupport (base.test : ℝ → ℂ)).trans hsuppBase
  have hcs := (subset_tsupport (correction.test : ℝ → ℂ)).trans hsuppCorrection
  have hbs2 := ((support_deriv_subset (f := deriv (base.test : ℝ → ℂ))).trans
    (tsupport_deriv_subset (f := (base.test : ℝ → ℂ)))).trans hsuppBase
  have hcs2 := ((support_deriv_subset (f := deriv (correction.test : ℝ → ℂ))).trans
    (tsupport_deriv_subset (f := (correction.test : ℝ → ℂ)))).trans hsuppCorrection
  intro sigma hsigma
  have hb := stripNorm_le_of_endpoint_bounds (base.test : ℝ → ℂ) base.test.continuous
    hbs hsigma (hbase _ (by simp)) (hbase _ (by simp))
  have hc := stripNorm_le_of_endpoint_bounds (correction.test : ℝ → ℂ) correction.test.continuous
    hcs hsigma (hcorrection _ (by simp)) (hcorrection _ (by simp))
  have hbd := stripSecondNorm_le_of_endpoint_bounds (base.test : ℝ → ℂ) hb2
    hbs2 hsigma (hbaseSecond _ (by simp)) (hbaseSecond _ (by simp))
  have hcd := stripSecondNorm_le_of_endpoint_bounds (correction.test : ℝ → ℂ) hc2
    hcs2 hsigma (hcorrectionSecond _ (by simp)) (hcorrectionSecond _ (by simp))
  exact (min_le_min
    (mul_le_mul hbd hc (stripNorm_nonneg _ _) (by norm_num [baseSecondUpper2343]))
    (mul_le_mul hcd hb (stripNorm_nonneg _ _) (by norm_num [correctionSecondUpper2343]))).trans
      endpoint_min_product_le_frozen

theorem frozenStripHypothesis_of_owner_endpoint_bounds
    (baseCoefficients correctionCoefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (hbase : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (correctedPhysical baseCoefficients modulations) ≤ baseNormUpper2343)
    (hbaseSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (correctedPhysical baseCoefficients modulations) ≤
        baseSecondUpper2343)
    (hcorrection : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (correctedPhysical correctionCoefficients modulations) ≤
        correctionNormUpper2343)
    (hcorrectionSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (correctedPhysical correctionCoefficients modulations) ≤
        correctionSecondUpper2343) :
    FrozenStripHypothesis (correctedPhysicalCompactLogTest baseCoefficients modulations)
      (correctedPhysicalCompactLogTest correctionCoefficients modulations) := by
  apply frozenStripHypothesis_of_compact_endpoint_bounds
    (correctedPhysicalCompactLogTest baseCoefficients modulations)
    (correctedPhysicalCompactLogTest correctionCoefficients modulations)
    (correctedPhysicalCompactLogTest_tsupport_subset _ _)
    (correctedPhysicalCompactLogTest_tsupport_subset _ _)
  · simpa only [correctedPhysicalCompactLogTest_toFun] using hbase
  · simpa only [correctedPhysicalCompactLogTest_toFun] using hbaseSecond
  · simpa only [correctedPhysicalCompactLogTest_toFun] using hcorrection
  · simpa only [correctedPhysicalCompactLogTest_toFun] using hcorrectionSecond

end ConnesWeilRH.Dev
