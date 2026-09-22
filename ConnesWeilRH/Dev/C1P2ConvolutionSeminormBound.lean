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
