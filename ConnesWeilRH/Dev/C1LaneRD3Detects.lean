/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1LaneRD3Root

/-!
# Lane R-D3, detects step: the frame theorem compressing premise 1 to the sign field

`C1LaneRD3Root` builds, for every compact-log test `h`, the differential root
`tripleVanishingRoot h = D_0 D_{1/2} D_1 h` whose bilateral Laplace transform
carries the Vandermonde factor `(0 - s) * (1/2 - s) * (1 - s)`.  This file
completes the detector side of the lane:

1. a concrete compact-log test with everywhere-nonzero Laplace value up to the
   exponential twist exists (`exists_compactLogTest_laplaceAt_ne_zero`);
2. the triple-vanishing root detects every point off the three nodes
   (`tripleVanishingRoot_laplaceAt_ne_zero`);
3. the frame theorem `healthyDetectorData_of_rootFrame_and_arch_pos`: a
   window-confined `h` with `laplaceAt h rho ≠ 0` and strict positivity of the
   archimedean term on the root's convolution square yields the full
   `HealthyYoshidaDetectorData rho (tripleVanishingRoot h)`;
4. the reduction theorem `CC20YoshidaDetectorExists_of_existsFrame_and_arch_pos`:
   premise 1 of the committed two-premise exit
   (`C1HealthyYoshidaDetector.healthy_spectral_nonneg_sourceRH_of_yoshida_detector`)
   follows from the interpolation frame — one window-confined test per
   off-critical zero with nonvanishing Laplace value — plus the archimedean
   sign field on the D3 squares.

No archimedean sign statement is asserted here; the sign field remains an
input, as required by the model-fidelity bookkeeping (the frame must not
manufacture positivity of its own).
-/

namespace ConnesWeilRH
namespace Source
namespace C1LaneRD3Detects

open MeasureTheory
open scoped ContDiff
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1LaneRD3Root

/-! ### A concrete nonzero compact-log test -/

/-- A concrete smooth compactly supported bump: a `ContDiffBump` centred at
the origin of the additive log coordinate, supported in `[-2, 2]` and equal to
one at `0`. -/
noncomputable def baseBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The complexified bump as a raw function of the additive log coordinate. -/
noncomputable def bumpRaw : ℝ → ℂ := fun x => ((baseBump x : ℝ) : ℂ)

theorem bumpRaw_contDiff : ContDiff ℝ ∞ bumpRaw :=
  Complex.ofRealCLM.contDiff.comp baseBump.contDiff

theorem bumpRaw_hasCompactSupport : HasCompactSupport bumpRaw :=
  HasCompactSupport.comp_left baseBump.hasCompactSupport rfl

/-- The concrete bump, packaged as a compact-log test. -/
noncomputable def bumpLogTest : CompactLogTest :=
  { test := bumpRaw_hasCompactSupport.toSchwartzMap bumpRaw_contDiff
    compactSupport := by simpa [bumpRaw] using bumpRaw_hasCompactSupport }

theorem bumpLogTest_apply (x : ℝ) :
    bumpLogTest.test x = ((baseBump x : ℝ) : ℂ) :=
  rfl

private theorem baseBump_integral_pos : 0 < ∫ x : ℝ, baseBump x := by
  have hcont : Continuous baseBump :=
    (baseBump.contDiff (n := ⊤)).continuous
  exact integral_pos_of_integrable_nonneg_nonzero (x := 0) hcont
    (hcont.integrable_of_hasCompactSupport baseBump.hasCompactSupport)
    (fun x => baseBump.nonneg' x)
    (by rw [baseBump.one_of_mem_closedBall
      (by show (0 : ℝ) ∈ Metric.closedBall 0 (1 : ℝ)
          simp [Metric.mem_closedBall])];
        norm_num)

/-- At the origin of the Laplace variable the concrete bump reads the positive
mass integral, so the Laplace value is nonzero. -/
theorem laplaceAt_bumpLogTest_zero_eq :
    CompactLogTest.laplaceAt bumpLogTest 0
      = ∫ x : ℝ, ((baseBump x : ℝ) : ℂ) := by
  unfold CompactLogTest.laplaceAt
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp [exponentialWeight_apply, bumpLogTest_apply]

theorem laplaceAt_bumpLogTest_zero_ne_zero :
    CompactLogTest.laplaceAt bumpLogTest 0 ≠ 0 := by
  rw [laplaceAt_bumpLogTest_zero_eq, integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt baseBump_integral_pos)

/-- A compact-log test with nonvanishing Laplace value exists at every point
of the complex plane: take the concrete bump and twist it by the exponential
weight `-rho`, which shifts the bilateral Laplace variable to the origin. -/
theorem exists_compactLogTest_laplaceAt_ne_zero (rho : ℂ) :
    ∃ h : CompactLogTest, CompactLogTest.laplaceAt h rho ≠ 0 :=
  ⟨exponentialWeight bumpLogTest (-rho), by
    have hshift : rho + (-rho) = (0 : ℂ) := by ring
    rw [C1SpectralWeil.laplaceAt_exponentialWeight_eq, hshift]
    exact laplaceAt_bumpLogTest_zero_ne_zero⟩

/-! ### The triple-vanishing root detects every off-node point -/

/-- The D3 root detects `rho` as soon as the seed test does and `rho` avoids
the three nodes: the Vandermonde factor `(0 - rho) * (1/2 - rho) * (1 - rho)`
is nonzero off `{0, 1/2, 1}`. -/
theorem tripleVanishingRoot_laplaceAt_ne_zero
    (h : CompactLogTest) {rho : ℂ}
    (hrho : CompactLogTest.laplaceAt h rho ≠ 0)
    (h0 : rho ≠ 0) (hhalf : rho ≠ 1 / 2) (hone : rho ≠ 1) :
    CompactLogTest.laplaceAt (tripleVanishingRoot h) rho ≠ 0 := by
  rw [laplaceAt_tripleVanishingRoot]
  refine mul_ne_zero
    (mul_ne_zero (mul_ne_zero (sub_ne_zero_of_ne (Ne.symm h0))
      (sub_ne_zero_of_ne (Ne.symm hhalf)))
      (sub_ne_zero_of_ne (Ne.symm hone))) hrho

/-! ### The frame theorem: premise 1 compressed to the sign field -/

/-- The frame theorem.  A seed test `h` confined to `[-w, w]` with `w < 3/10`,
nonvanishing Laplace value at `rho ∉ {0, 1/2, 1}`, and STRICT POSITIVITY of
the archimedean term on the D3 square produces the full healthy detector data
at `rho`.  The sign field is an input: the frame itself only transports
nondegeneracy, window confinement, and the vanishing structure. -/
theorem healthyDetectorData_of_rootFrame_and_arch_pos
    (rho : ℂ) (h : CompactLogTest) {w : ℝ}
    (hsupport : Function.support (h.test : ℝ → ℂ) ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : ℝ))
    (hrho : CompactLogTest.laplaceAt h rho ≠ 0)
    (h0 : rho ≠ 0) (hhalf : rho ≠ 1 / 2) (hone : rho ≠ 1)
    (harch : 0 < C1SameOwnerWeil.archimedeanTerm
      (tripleVanishingRoot h).convolutionSquare) :
    C1HealthyYoshidaDetector.HealthyYoshidaDetectorData rho
      (tripleVanishingRoot h) where
  compactSupportSmooth := C1.healthyCC20CompactSupportSmooth _
  vanishesOnF := tripleVanishingRoot_vanishesOn_cc20Triple h
  detectsRho := tripleVanishingRoot_laplaceAt_ne_zero h hrho h0 hhalf hone
  weilSquareSumPositive :=
    (C1HealthyYoshidaDetector.weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple
      (tripleVanishingRoot h) (tripleVanishingRoot_vanishesOn_cc20Triple h)
      (tripleVanishingRoot_square_support_subset_open_log_two_of_Icc h hsupport
        hw)).mpr harch

/-- The reduction of premise 1: detector existence on the healthy owner
follows from (a) the interpolation frame — for every off-critical source zero
a window-confined seed test with nonvanishing Laplace value and the strict
archimedean sign on its D3 square — composed with the committed packing.
The interpolation engine (`C1LaneRD3Root`) and the detector transport
(this file) are fully committed; what remains open is exactly the sign field
plus the window-confined frame at each off-critical zero. -/
theorem CC20YoshidaDetectorExists_of_existsFrame_and_arch_pos
    (hex : ∀ {rho : ℂ},
      RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re ≠ 1 / 2 →
          ∃ (h : CompactLogTest) (w : ℝ),
            Function.support (h.test : ℝ → ℂ) ⊆ Set.Icc (-w) w ∧
              w < (3 / 10 : ℝ) ∧
              CompactLogTest.laplaceAt h rho ≠ 0 ∧
              0 < C1SameOwnerWeil.archimedeanTerm
                (tripleVanishingRoot h).convolutionSquare) :
    CC20YoshidaDetectorExists C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine
    C1HealthyYoshidaDetector.healthyCC20YoshidaDetectorExists_of_healthyDetectorData
      ?_
  intro rho hrho hoff
  rcases hex hrho hoff with ⟨h, w, hsupp, hw, hlap, harch⟩
  have h0 : rho ≠ 0 := by
    simpa [criticalVanishingPointValue] using
      standard_source_nontrivial_zero_ne_cc20_zero hrho
  have hhalf : rho ≠ (1 / 2 : ℂ) := by
    simpa [criticalVanishingPointValue] using
      standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff
  have hone : rho ≠ 1 := by
    simpa [criticalVanishingPointValue] using
      standard_source_nontrivial_zero_ne_cc20_one hrho
  exact ⟨tripleVanishingRoot h,
    healthyDetectorData_of_rootFrame_and_arch_pos rho h hsupp hw hlap h0 hhalf
      hone harch⟩

end C1LaneRD3Detects
end Source
end ConnesWeilRH
