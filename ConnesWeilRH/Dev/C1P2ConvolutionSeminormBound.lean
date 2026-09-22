/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootConvolutionNorm
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback
import ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling
import ConnesWeilRH.Dev.C1P2DirectSupportOverlapDecoupling

/-!
# C1P2ConvolutionSeminormBound - L^∞ seminorm decay under convolution

This module establishes the fundamental L^∞ (order 0-0 Schwartz seminorm)
bound for convolutions of compactly supported test functions:
`seminorm (f * g) ≤ ‖f‖_{L¹} * seminorm(g) ≤ (c - a) * seminorm(f) * seminorm(g)`.

Consumer: Orbit factor seminorm decay in the healthy CompactLog Option A route.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2ConvolutionSeminormBound

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CCM24FiniteSRootConvolutionNorm
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalProfileReadback
open C1P2DirectChebyshevDecoupling
open C1P2DirectSupportOverlapDecoupling
open C1SameOwnerWeil

noncomputable section

/-- Pointwise bound on the convolution integrand by the L^∞ seminorm of the right factor. -/
theorem norm_convolution_integrand_le_seminorm
    (f g : CompactLogTest) (x t : ℝ) :
    ‖f.test t * g.test (x - t)‖ ≤
      ‖f.test t‖ * SchwartzMap.seminorm ℂ 0 0 g.test := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (SchwartzMap.norm_le_seminorm ℂ g.test (x - t))
    (norm_nonneg _)

/-- The convolution integrand is integrable on the real line. -/
theorem integrable_convolution_integrand
    (f g : CompactLogTest) (x : ℝ) :
    Integrable (fun t : ℝ => f.test t * g.test (x - t)) volume := by
  have hcont_g : Continuous (fun t : ℝ => g.test (x - t)) :=
    g.test.continuous.comp (continuous_const.sub continuous_id)
  have hcont : Continuous (fun t : ℝ => f.test t * g.test (x - t)) :=
    f.test.continuous.mul hcont_g
  have hmeas : AEStronglyMeasurable (fun t : ℝ => f.test t * g.test (x - t)) volume :=
    hcont.aestronglyMeasurable
  let S := SchwartzMap.seminorm ℂ 0 0 g.test
  have hS_int : Integrable (fun t : ℝ => ‖f.test t‖ * S) volume :=
    f.test.integrable.norm.mul_const S
  have hbound : ∀ᵐ t ∂volume, ‖f.test t * g.test (x - t)‖ ≤ ‖f.test t‖ * S := by
    filter_upwards with t
    exact norm_convolution_integrand_le_seminorm f g x t
  exact hS_int.mono' hmeas hbound

/-- Pointwise evaluation of a convolution is bounded by the L¹ norm of the left factor
    times the L^∞ seminorm of the right factor. -/
theorem norm_convolution_apply_le_seminorm
    (f g : CompactLogTest) (x : ℝ) :
    ‖(f.convolution g).test x‖ ≤
      (∫ t : ℝ, ‖f.test t‖) * SchwartzMap.seminorm ℂ 0 0 g.test := by
  rw [CompactLogTest.convolution_apply]
  have h_le : ‖∫ t : ℝ, f.test t * g.test (x - t)‖ ≤ ∫ t : ℝ, ‖f.test t * g.test (x - t)‖ :=
    norm_integral_le_integral_norm (μ := volume) (fun t : ℝ => f.test t * g.test (x - t))
  apply h_le.trans
  have h_int_le :
      (∫ t : ℝ, ‖f.test t * g.test (x - t)‖) ≤
        ∫ t : ℝ, ‖f.test t‖ * SchwartzMap.seminorm ℂ 0 0 g.test := by
    apply integral_mono
    · exact (integrable_convolution_integrand f g x).norm
    · exact f.test.integrable.norm.mul_const _
    · intro t
      exact norm_convolution_integrand_le_seminorm f g x t
  apply h_int_le.trans
  rw [integral_mul_const]

/-- The L^∞ seminorm of a convolution is bounded by the L¹ norm of the left factor
    times the L^∞ seminorm of the right factor. -/
theorem seminorm_convolution_le_integral_mul_seminorm
    (f g : CompactLogTest) :
    SchwartzMap.seminorm ℂ 0 0 (f.convolution g).test ≤
      (∫ t : ℝ, ‖f.test t‖) * SchwartzMap.seminorm ℂ 0 0 g.test := by
  have hnonneg : 0 ≤ (∫ t : ℝ, ‖f.test t‖) * SchwartzMap.seminorm ℂ 0 0 g.test := by
    apply mul_nonneg
    · exact integral_nonneg (fun _ => norm_nonneg _)
    · positivity
  apply SchwartzMap.seminorm_le_bound ℂ 0 0 _ hnonneg
  intro x
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
    norm_convolution_apply_le_seminorm f g x

/-- The L^∞ seminorm of a convolution is bounded by the L¹ toLp norm of the left factor
    times the L^∞ seminorm of the right factor. -/
theorem seminorm_convolution_le_toLp_one_mul_seminorm
    (f g : CompactLogTest) :
    SchwartzMap.seminorm ℂ 0 0 (f.convolution g).test ≤
      ‖f.test.toLp 1‖ * SchwartzMap.seminorm ℂ 0 0 g.test := by
  rw [SchwartzMap.norm_toLp_one]
  exact seminorm_convolution_le_integral_mul_seminorm f g

/-- For compactly supported tests, the L^∞ seminorm of the convolution is bounded
    by the support interval length times the product of the individual seminorms. -/
theorem seminorm_convolution_le_supportLength_mul_seminorm
    (f g : CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support f.test ⊆ Set.Icc a c) :
    SchwartzMap.seminorm ℂ 0 0 (f.convolution g).test ≤
      (c - a) * SchwartzMap.seminorm ℂ 0 0 f.test *
        SchwartzMap.seminorm ℂ 0 0 g.test := by
  have htoLp := norm_toLp_one_le_supportLength_mul_seminorm f.test a c hac hsupp
  have hsem := seminorm_convolution_le_toLp_one_mul_seminorm f g
  have hstep : ‖f.test.toLp 1‖ * SchwartzMap.seminorm ℂ 0 0 g.test ≤
      (c - a) * SchwartzMap.seminorm ℂ 0 0 f.test * SchwartzMap.seminorm ℂ 0 0 g.test := by
    have h1 : ‖f.test.toLp 1‖ * SchwartzMap.seminorm ℂ 0 0 g.test ≤
        ((c - a) * SchwartzMap.seminorm ℂ 0 0 f.test) * SchwartzMap.seminorm ℂ 0 0 g.test :=
      mul_le_mul_of_nonneg_right htoLp (by positivity)
    have h2 : ((c - a) * SchwartzMap.seminorm ℂ 0 0 f.test) * SchwartzMap.seminorm ℂ 0 0 g.test =
        (c - a) * SchwartzMap.seminorm ℂ 0 0 f.test * SchwartzMap.seminorm ℂ 0 0 g.test := by ring
    linarith
  exact hsem.trans hstep

/-- Pointwise commutativity of the log-coordinate convolution. -/
theorem convolution_apply_comm (f g : CompactLogTest) (x : ℝ) :
    (f.convolution g).test x = (g.convolution f).test x := by
  rw [CompactLogTest.convolution_apply, CompactLogTest.convolution_apply]
  have h_sub := (integral_sub_left_eq_self (fun t : ℝ => f.test t * g.test (x - t)) volume x).symm
  rw [h_sub]
  apply integral_congr_ae
  filter_upwards with t
  simp only [sub_sub_cancel]
  ring

/-- Commutativity of the L^∞ order 0-0 Schwartz seminorm of a convolution. -/
theorem seminorm_convolution_comm (f g : CompactLogTest) :
    SchwartzMap.seminorm ℂ 0 0 (f.convolution g).test =
      SchwartzMap.seminorm ℂ 0 0 (g.convolution f).test := by
  have heq : (f.convolution g).test = (g.convolution f).test := by
    ext x
    exact convolution_apply_comm f g x
  rw [heq]

/-- When the right factor has compact support in `[a, c]`, the convolution seminorm
    satisfies the same support-length bound by commutativity. -/
theorem seminorm_convolution_le_supportLength_mul_seminorm_right
    (f g : CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    SchwartzMap.seminorm ℂ 0 0 (f.convolution g).test ≤
      (c - a) * SchwartzMap.seminorm ℂ 0 0 g.test *
        SchwartzMap.seminorm ℂ 0 0 f.test := by
  rw [seminorm_convolution_comm]
  exact seminorm_convolution_le_supportLength_mul_seminorm g f a c hac hsupp

/-- The order 0-0 Schwartz seminorm of an iterated convolution contracts
    geometrically with contraction factor `(c - a) * seminorm(f)`. -/
theorem seminorm_convolutionIterate_le_pow
    (f : CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support f.test ⊆ Set.Icc a c) (n : ℕ) :
    SchwartzMap.seminorm ℂ 0 0 (convolutionIterate f n).test ≤
      ((c - a) * SchwartzMap.seminorm ℂ 0 0 f.test) ^ n *
        SchwartzMap.seminorm ℂ 0 0 f.test := by
  induction n with
  | zero =>
    simp only [convolutionIterate_zero, pow_zero, one_mul, le_refl]
  | succ n ih =>
    rw [convolutionIterate_succ]
    have hstep := seminorm_convolution_le_supportLength_mul_seminorm_right
      (convolutionIterate f n) f a c hac hsupp
    have hih : (c - a) * SchwartzMap.seminorm ℂ 0 0 f.test *
        SchwartzMap.seminorm ℂ 0 0 (convolutionIterate f n).test ≤
      ((c - a) * SchwartzMap.seminorm ℂ 0 0 f.test) ^ (n + 1) *
        SchwartzMap.seminorm ℂ 0 0 f.test := by
      calc
        (c - a) * SchwartzMap.seminorm ℂ 0 0 f.test *
            SchwartzMap.seminorm ℂ 0 0 (convolutionIterate f n).test ≤
          (c - a) * SchwartzMap.seminorm ℂ 0 0 f.test *
            (((c - a) * SchwartzMap.seminorm ℂ 0 0 f.test) ^ n *
              SchwartzMap.seminorm ℂ 0 0 f.test) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((c - a) * SchwartzMap.seminorm ℂ 0 0 f.test) ^ (n + 1) *
              SchwartzMap.seminorm ℂ 0 0 f.test := by
          rw [pow_succ]
          ring
    exact hstep.trans hih

/-- The raw factor seminorm of an OrbitG8Geometry contracts geometrically in the
    orbit index `n`, bounded by `2 * ((2 * S_base) ^ n * S_base) * S_corr`. -/
theorem rawFactorSeminorm_le_geometric_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    rawFactorSeminorm geometry ≤
      (2 : ℝ) *
        (((2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.base.test) ^ geometry.orbitIndex *
          SchwartzMap.seminorm ℂ 0 0 geometry.base.test) *
        SchwartzMap.seminorm ℂ 0 0 geometry.correction.test := by
  unfold rawFactorSeminorm orbitRawFactor
  have hbase_supp : Function.support geometry.base.test ⊆ Set.Icc (-1 : ℝ) 1 :=
    geometry.base_support.trans Set.Ioo_subset_Icc_self
  have hbase_len : (1 : ℝ) - (-1) = 2 := by ring
  have hcorr_supp : Function.support geometry.correction.test ⊆ Set.Icc (-1 : ℝ) 1 :=
    geometry.correction_support.trans Set.Ioo_subset_Icc_self
  have hcorr_len : (1 : ℝ) - (-1) = 2 := by ring
  have hbound := seminorm_convolution_le_supportLength_mul_seminorm_right
    (convolutionIterate geometry.base geometry.orbitIndex) geometry.correction
    (-1) 1 (by norm_num) hcorr_supp
  rw [hcorr_len] at hbound
  have hiter := seminorm_convolutionIterate_le_pow
    geometry.base (-1) 1 (by norm_num) hbase_supp geometry.orbitIndex
  rw [hbase_len] at hiter
  have hmul : (2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.correction.test *
      SchwartzMap.seminorm ℂ 0 0 (convolutionIterate geometry.base geometry.orbitIndex).test ≤
    (2 : ℝ) *
      (((2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.base.test) ^ geometry.orbitIndex *
        SchwartzMap.seminorm ℂ 0 0 geometry.base.test) *
      SchwartzMap.seminorm ℂ 0 0 geometry.correction.test := by
    calc
      (2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.correction.test *
          SchwartzMap.seminorm ℂ 0 0 (convolutionIterate geometry.base geometry.orbitIndex).test ≤
        (2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.correction.test *
          (((2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.base.test) ^ geometry.orbitIndex *
            SchwartzMap.seminorm ℂ 0 0 geometry.base.test) :=
        mul_le_mul_of_nonneg_left hiter (by positivity)
      _ = (2 : ℝ) *
            (((2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.base.test) ^ geometry.orbitIndex *
              SchwartzMap.seminorm ℂ 0 0 geometry.base.test) *
            SchwartzMap.seminorm ℂ 0 0 geometry.correction.test := by ring
  exact hbound.trans hmul

/-- The raw factor seminorm of an OrbitG8Geometry is bounded by the product of the
    iterated base L¹ norm and the correction seminorm. -/
theorem rawFactorSeminorm_le_toLp_one_mul_seminorm
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    rawFactorSeminorm geometry ≤
      ‖(convolutionIterate geometry.base geometry.orbitIndex).test.toLp 1‖ *
        SchwartzMap.seminorm ℂ 0 0 geometry.correction.test := by
  unfold rawFactorSeminorm orbitRawFactor
  exact seminorm_convolution_le_toLp_one_mul_seminorm
    (convolutionIterate geometry.base geometry.orbitIndex) geometry.correction

/-- Full exit connecting geometric decay of the raw factor seminorm to SourceRH. -/
theorem sourceRH_of_geometric_contraction_and_harmonicBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ delta : Real,
              0 ≤ delta ∧
              delta ≤ -archimedeanTerm g.convolutionSquare ∧
              (2 : ℝ) *
                (((2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.base.test) ^ geometry.orbitIndex *
                  SchwartzMap.seminorm ℂ 0 0 geometry.base.test) *
                SchwartzMap.seminorm ℂ 0 0 geometry.correction.test ≤
                  harmonicBudgetSeminorm geometry delta) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_harmonicBudgetSeminorm
  intro rho hright
  obtain ⟨g, geometry, delta, hdelta, hmargin, hgeom⟩ := hproducer rho hright
  have hS := (rawFactorSeminorm_le_geometric_bound geometry).trans hgeom
  exact ⟨g, geometry, delta, hdelta, hmargin, hS⟩

/-- Full exit connecting geometric decay of the raw factor seminorm to Mathlib canonical
    RiemannHypothesis. -/
theorem riemannHypothesis_of_geometric_contraction_and_harmonicBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ delta : Real,
              0 ≤ delta ∧
              delta ≤ -archimedeanTerm g.convolutionSquare ∧
              (2 : ℝ) *
                (((2 : ℝ) * SchwartzMap.seminorm ℂ 0 0 geometry.base.test) ^ geometry.orbitIndex *
                  SchwartzMap.seminorm ℂ 0 0 geometry.base.test) *
                SchwartzMap.seminorm ℂ 0 0 geometry.correction.test ≤
                  harmonicBudgetSeminorm geometry delta) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_harmonicBudgetSeminorm
  intro rho hright
  obtain ⟨g, geometry, delta, hdelta, hmargin, hgeom⟩ := hproducer rho hright
  have hS := (rawFactorSeminorm_le_geometric_bound geometry).trans hgeom
  exact ⟨g, geometry, delta, hdelta, hmargin, hS⟩

/-- Full exit connecting L¹ toLp decay of the iterated base to SourceRH. -/
theorem sourceRH_of_iteratedBase_decay_and_harmonicBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ delta : Real,
              0 ≤ delta ∧
              delta ≤ -archimedeanTerm g.convolutionSquare ∧
              ‖(convolutionIterate geometry.base geometry.orbitIndex).test.toLp 1‖ *
                SchwartzMap.seminorm ℂ 0 0 geometry.correction.test ≤
                  harmonicBudgetSeminorm geometry delta) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_harmonicBudgetSeminorm
  intro rho hright
  obtain ⟨g, geometry, delta, hdelta, hmargin, hdecay⟩ := hproducer rho hright
  have hS := (rawFactorSeminorm_le_toLp_one_mul_seminorm geometry).trans hdecay
  exact ⟨g, geometry, delta, hdelta, hmargin, hS⟩

/-- Full exit connecting L¹ toLp decay of the iterated base to Mathlib canonical
    RiemannHypothesis. -/
theorem riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ delta : Real,
              0 ≤ delta ∧
              delta ≤ -archimedeanTerm g.convolutionSquare ∧
              ‖(convolutionIterate geometry.base geometry.orbitIndex).test.toLp 1‖ *
                SchwartzMap.seminorm ℂ 0 0 geometry.correction.test ≤
                  harmonicBudgetSeminorm geometry delta) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_harmonicBudgetSeminorm
  intro rho hright
  obtain ⟨g, geometry, delta, hdelta, hmargin, hdecay⟩ := hproducer rho hright
  have hS := (rawFactorSeminorm_le_toLp_one_mul_seminorm geometry).trans hdecay
  exact ⟨g, geometry, delta, hdelta, hmargin, hS⟩

end
end C1P2ConvolutionSeminormBound
end Source
end ConnesWeilRH
