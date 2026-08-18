/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1XiCenterTwoGammaConstrainedPrefix

/-!
# C1XiCenterTwoGammaComplexSplit - real/imaginary owner decomposition

For a complex compact-log root `g`, this module constructs the two real-valued
component tests and proves the exact decomposition of the Hermitian convolution
square at the archimedean owner.  The same decomposition is carried through
the Gamma_R profile integrals and the fixed `N = 21` prefix.

The module intentionally does not infer prime-free support for the component
squares from prime-free support of the complex square.  The cross convolution
can cancel in the imaginary channel, so that implication requires a separate
root-support hypothesis.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaComplexSplit

open CCM25Concrete.CompactLogConvolution
open MeasureTheory
open scoped ContDiff
open scoped ComplexConjugate

noncomputable section

set_option maxHeartbeats 800000 in
def realPartTest (g : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := Complex.ofRealCLM ∘ Complex.reCLM ∘ g.test
  have hinnerCompact : HasCompactSupport (Complex.reCLM ∘ g.test) := by
    apply g.compactSupport.comp_left
    rfl
  have hcompact : HasCompactSupport raw := by
    simpa [raw] using hinnerCompact.comp_left (by rfl)
  have hinnerSmooth : ContDiff ℝ ∞ (Complex.reCLM ∘ g.test) := by
    exact Complex.reCLM.contDiff.comp (g.test.smooth ⊤)
  have hsmooth : ContDiff ℝ ∞ raw := by
    simpa [raw] using Complex.ofRealCLM.contDiff.comp hinnerSmooth
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

set_option maxHeartbeats 800000 in
def imagPartTest (g : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := Complex.ofRealCLM ∘ Complex.imCLM ∘ g.test
  have hinnerCompact : HasCompactSupport (Complex.imCLM ∘ g.test) := by
    apply g.compactSupport.comp_left
    rfl
  have hcompact : HasCompactSupport raw := by
    simpa [raw] using hinnerCompact.comp_left (by rfl)
  have hinnerSmooth : ContDiff ℝ ∞ (Complex.imCLM ∘ g.test) := by
    exact Complex.imCLM.contDiff.comp (g.test.smooth ⊤)
  have hsmooth : ContDiff ℝ ∞ raw := by
    simpa [raw] using Complex.ofRealCLM.contDiff.comp hinnerSmooth
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem realPartTest_apply (g : CompactLogTest) (x : ℝ) :
    (realPartTest g).test x = Complex.ofReal (g.test x).re := by
  simp [realPartTest]

@[simp] theorem imagPartTest_apply (g : CompactLogTest) (x : ℝ) :
    (imagPartTest g).test x = Complex.ofReal (g.test x).im := by
  simp [imagPartTest]

theorem test_eq_realPart_add_I_imagPart (g : CompactLogTest) (x : ℝ) :
    g.test x = (realPartTest g).test x + Complex.I * (imagPartTest g).test x := by
  rw [realPartTest_apply, imagPartTest_apply]
  apply Complex.ext <;> simp

theorem laplaceAt_eq_realPart_add_I_imagPart
    (g : CompactLogTest) (s : ℂ) :
    CC20YoshidaConvolution.CompactLogTest.laplaceAt g s =
      CC20YoshidaConvolution.CompactLogTest.laplaceAt (realPartTest g) s +
        Complex.I *
          CC20YoshidaConvolution.CompactLogTest.laplaceAt (imagPartTest g) s := by
  unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  have hreal : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * (realPartTest g).test x) := by
    simpa only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply] using
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight
        (realPartTest g) s).test.integrable
  have himag : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * (imagPartTest g).test x) := by
    simpa only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply] using
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight
        (imagPartTest g) s).test.integrable
  rw [← integral_const_mul]
  rw [← integral_add hreal (himag.const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards with x
  rw [test_eq_realPart_add_I_imagPart]
  ring

private theorem laplaceAt_realPart_im_eq_zero
    (g : CompactLogTest) (s : ℝ) :
    (CC20YoshidaConvolution.CompactLogTest.laplaceAt
      (realPartTest g) (s : ℂ)).im = 0 := by
  unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  have hintegrable : Integrable (fun x : ℝ =>
      Complex.exp ((s : ℂ) * (x : ℂ)) * (realPartTest g).test x) := by
    simpa only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply] using
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight
        (realPartTest g) (s : ℂ)).test.integrable
  calc
    (∫ x : ℝ,
        Complex.exp ((s : ℂ) * (x : ℂ)) * (realPartTest g).test x).im =
        ∫ x : ℝ,
          (Complex.exp ((s : ℂ) * (x : ℂ)) *
            (realPartTest g).test x).im := by
      symm
      simpa only [Complex.imCLM_apply] using
        (Complex.imCLM.integral_comp_comm hintegrable)
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with x
      rw [realPartTest_apply]
      have hexpim :
          (Complex.exp ((s : ℂ) * (x : ℂ))).im = 0 := by
        rw [show (s : ℂ) * (x : ℂ) = ((s * x : ℝ) : ℂ) by
          push_cast
          rfl]
        exact Complex.exp_ofReal_im (s * x)
      rw [Complex.mul_im, hexpim]
      simp

private theorem laplaceAt_imagPart_im_eq_zero
    (g : CompactLogTest) (s : ℝ) :
    (CC20YoshidaConvolution.CompactLogTest.laplaceAt
      (imagPartTest g) (s : ℂ)).im = 0 := by
  unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  have hintegrable : Integrable (fun x : ℝ =>
      Complex.exp ((s : ℂ) * (x : ℂ)) * (imagPartTest g).test x) := by
    simpa only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply] using
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight
        (imagPartTest g) (s : ℂ)).test.integrable
  calc
    (∫ x : ℝ,
        Complex.exp ((s : ℂ) * (x : ℂ)) * (imagPartTest g).test x).im =
        ∫ x : ℝ,
          (Complex.exp ((s : ℂ) * (x : ℂ)) *
            (imagPartTest g).test x).im := by
      symm
      simpa only [Complex.imCLM_apply] using
        (Complex.imCLM.integral_comp_comm hintegrable)
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with x
      rw [imagPartTest_apply]
      have hexpim :
          (Complex.exp ((s : ℂ) * (x : ℂ))).im = 0 := by
        rw [show (s : ℂ) * (x : ℂ) = ((s * x : ℝ) : ℂ) by
          push_cast
          rfl]
        exact Complex.exp_ofReal_im (s * x)
      rw [Complex.mul_im, hexpim]
      simp

theorem laplaceAt_realPart_eq_zero_of_eq_zero
    {g : CompactLogTest} {s : ℝ}
    (hg : CC20YoshidaConvolution.CompactLogTest.laplaceAt g (s : ℂ) = 0) :
    CC20YoshidaConvolution.CompactLogTest.laplaceAt
      (realPartTest g) (s : ℂ) = 0 := by
  have hsplit := laplaceAt_eq_realPart_add_I_imagPart g (s : ℂ)
  have himag := laplaceAt_imagPart_im_eq_zero g s
  rw [hg] at hsplit
  apply Complex.ext
  · have h := congrArg Complex.re hsplit
    simpa [Complex.mul_re, himag] using h.symm
  · exact laplaceAt_realPart_im_eq_zero g s

theorem laplaceAt_imagPart_eq_zero_of_eq_zero
    {g : CompactLogTest} {s : ℝ}
    (hg : CC20YoshidaConvolution.CompactLogTest.laplaceAt g (s : ℂ) = 0) :
    CC20YoshidaConvolution.CompactLogTest.laplaceAt
      (imagPartTest g) (s : ℂ) = 0 := by
  have hsplit := laplaceAt_eq_realPart_add_I_imagPart g (s : ℂ)
  have hreal := laplaceAt_realPart_im_eq_zero g s
  rw [hg] at hsplit
  apply Complex.ext
  · have h := congrArg Complex.im hsplit
    simpa [Complex.mul_im, hreal] using h.symm
  · exact laplaceAt_imagPart_im_eq_zero g s

theorem realPartTest_satisfies_laneRTripleVanishing
    {g : CompactLogTest} (hvanishes :
      C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing g) :
    C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing
      (realPartTest g) := by
  intro p hp
  cases p with
  | zero =>
      have hg :=
        C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing_laplaceAt_zero
          hvanishes
      have hr := laplaceAt_realPart_eq_zero_of_eq_zero (s := (0 : ℝ)) hg
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hr
  | half =>
      have hg :=
        C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing_laplaceAt_half
          hvanishes
      have hg' :
          CC20YoshidaConvolution.CompactLogTest.laplaceAt g
              ((1 / 2 : ℝ) : ℂ) = 0 := by
        simpa using hg
      have hr := laplaceAt_realPart_eq_zero_of_eq_zero
        (s := (1 / 2 : ℝ)) hg'
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hr
  | one =>
      have hg :=
        C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing_laplaceAt_one
          hvanishes
      have hr := laplaceAt_realPart_eq_zero_of_eq_zero (s := (1 : ℝ)) hg
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hr

theorem imagPartTest_satisfies_laneRTripleVanishing
    {g : CompactLogTest} (hvanishes :
      C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing g) :
    C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing
      (imagPartTest g) := by
  intro p hp
  cases p with
  | zero =>
      have hg :=
        C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing_laplaceAt_zero
          hvanishes
      have hi := laplaceAt_imagPart_eq_zero_of_eq_zero (s := (0 : ℝ)) hg
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hi
  | half =>
      have hg :=
        C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing_laplaceAt_half
          hvanishes
      have hg' :
          CC20YoshidaConvolution.CompactLogTest.laplaceAt g
              ((1 / 2 : ℝ) : ℂ) = 0 := by
        simpa using hg
      have hi := laplaceAt_imagPart_eq_zero_of_eq_zero
        (s := (1 / 2 : ℝ)) hg'
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hi
  | one =>
      have hg :=
        C1XiCenterTwoGammaConstrainedPrefix.laneRTripleVanishing_laplaceAt_one
          hvanishes
      have hi := laplaceAt_imagPart_eq_zero_of_eq_zero (s := (1 : ℝ)) hg
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hi

private theorem convolutionSquare_integrable_integrand
    (g : CompactLogTest) (x : ℝ) :
    Integrable (fun t : ℝ =>
      star (g.test (-t)) * g.test (x - t)) := by
  have hreflect : HasCompactSupport (fun t : ℝ => g.test (-t)) := by
    simpa using g.compactSupport.comp_homeomorph (Homeomorph.neg ℝ)
  have hstar : HasCompactSupport (fun t : ℝ => star (g.test (-t))) := by
    exact hreflect.comp_left (by simp)
  have hprod : HasCompactSupport (fun t : ℝ =>
      star (g.test (-t)) * g.test (x - t)) := by
    exact hstar.mul_right
  have hcont : Continuous (fun t : ℝ =>
      star (g.test (-t)) * g.test (x - t)) := by
    fun_prop
  exact hcont.integrable_of_hasCompactSupport hprod

private theorem convolutionSquare_integrand_re_split
    (g : CompactLogTest) (x t : ℝ) :
    (star (g.test (-t)) * g.test (x - t)).re =
      (star ((realPartTest g).test (-t)) *
          (realPartTest g).test (x - t)).re +
        (star ((imagPartTest g).test (-t)) *
          (imagPartTest g).test (x - t)).re := by
  rw [test_eq_realPart_add_I_imagPart g (-t),
    test_eq_realPart_add_I_imagPart g (x - t)]
  simp only [realPartTest_apply, imagPartTest_apply, Complex.star_def,
    Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem convolutionSquare_re_split (g : CompactLogTest) (x : ℝ) :
    (g.convolutionSquare.test x).re =
      ((realPartTest g).convolutionSquare.test x).re +
        ((imagPartTest g).convolutionSquare.test x).re := by
  rw [CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_apply,
    CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_apply,
    CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
  have hgre :
      (∫ t : ℝ, star (g.test (-t)) * g.test (x - t)).re =
        ∫ t : ℝ, (star (g.test (-t)) * g.test (x - t)).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm
        (convolutionSquare_integrable_integrand g x))
  have hreal :
      (∫ t : ℝ,
        star ((realPartTest g).test (-t)) *
          (realPartTest g).test (x - t)).re =
        ∫ t : ℝ,
          (star ((realPartTest g).test (-t)) *
            (realPartTest g).test (x - t)).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm
        (convolutionSquare_integrable_integrand (realPartTest g) x))
  have himag :
      (∫ t : ℝ,
        star ((imagPartTest g).test (-t)) *
          (imagPartTest g).test (x - t)).re =
        ∫ t : ℝ,
          (star ((imagPartTest g).test (-t)) *
            (imagPartTest g).test (x - t)).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm
        (convolutionSquare_integrable_integrand (imagPartTest g) x))
  rw [hgre, hreal, himag]
  calc
    (∫ t : ℝ, (star (g.test (-t)) * g.test (x - t)).re) =
        ∫ t : ℝ,
          (star ((realPartTest g).test (-t)) *
              (realPartTest g).test (x - t)).re +
            (star ((imagPartTest g).test (-t)) *
              (imagPartTest g).test (x - t)).re := by
      apply integral_congr_ae
      filter_upwards with t
      exact convolutionSquare_integrand_re_split g x t
    _ = (∫ t : ℝ,
        (star ((realPartTest g).test (-t)) *
          (realPartTest g).test (x - t)).re) +
        ∫ t : ℝ,
          (star ((imagPartTest g).test (-t)) *
            (imagPartTest g).test (x - t)).re :=
      integral_add
        (convolutionSquare_integrable_integrand (realPartTest g) x).re
        (convolutionSquare_integrable_integrand (imagPartTest g) x).re

theorem archimedeanNumerator_re_split
    (g : CompactLogTest) (y : ℝ) :
    (C1SameOwnerWeil.archimedeanNumerator g.convolutionSquare y).re =
      (C1SameOwnerWeil.archimedeanNumerator
        (realPartTest g).convolutionSquare y).re +
        (C1SameOwnerWeil.archimedeanNumerator
          (imagPartTest g).convolutionSquare y).re := by
  unfold C1SameOwnerWeil.archimedeanNumerator
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofRealCLM_apply, Complex.ofReal_re, Complex.ofReal_im]
  rw [convolutionSquare_re_split g y,
    convolutionSquare_re_split g (-y), convolutionSquare_re_split g 0]
  rw [g.convolutionSquare_zero_im,
    (realPartTest g).convolutionSquare_zero_im,
    (imagPartTest g).convolutionSquare_zero_im]
  norm_num
  ring

theorem archimedeanIntegrand_re_split
    (g : CompactLogTest) (y : ℝ) :
    (C1SameOwnerWeil.archimedeanIntegrand g.convolutionSquare y).re =
      (C1SameOwnerWeil.archimedeanIntegrand
        (realPartTest g).convolutionSquare y).re +
        (C1SameOwnerWeil.archimedeanIntegrand
          (imagPartTest g).convolutionSquare y).re := by
  unfold C1SameOwnerWeil.archimedeanIntegrand
  simp only [Complex.div_ofReal_re]
  rw [archimedeanNumerator_re_split g y]
  ring

theorem archimedeanTerm_split (g : CompactLogTest) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare =
      C1SameOwnerWeil.archimedeanTerm
        (realPartTest g).convolutionSquare +
        C1SameOwnerWeil.archimedeanTerm
          (imagPartTest g).convolutionSquare := by
  unfold C1SameOwnerWeil.archimedeanTerm
  have hF := C1SameOwnerWeil.archimedeanIntegrand_square_integrableOn_Ioi g
  have hR := C1SameOwnerWeil.archimedeanIntegrand_square_integrableOn_Ioi
    (realPartTest g)
  have hI := C1SameOwnerWeil.archimedeanIntegrand_square_integrableOn_Ioi
    (imagPartTest g)
  have hFsplit :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        C1SameOwnerWeil.archimedeanIntegrand g.convolutionSquare y).re =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1SameOwnerWeil.archimedeanIntegrand g.convolutionSquare y).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hF)
  have hRsplit :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        C1SameOwnerWeil.archimedeanIntegrand
          (realPartTest g).convolutionSquare y).re =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1SameOwnerWeil.archimedeanIntegrand
            (realPartTest g).convolutionSquare y).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hR)
  have hIsplit :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        C1SameOwnerWeil.archimedeanIntegrand
          (imagPartTest g).convolutionSquare y).re =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1SameOwnerWeil.archimedeanIntegrand
            (imagPartTest g).convolutionSquare y).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hI)
  have hRre : IntegrableOn
      (fun y : ℝ =>
        (C1SameOwnerWeil.archimedeanIntegrand
          (realPartTest g).convolutionSquare y).re)
      (Set.Ioi (0 : ℝ)) := hR.re
  have hIre : IntegrableOn
      (fun y : ℝ =>
        (C1SameOwnerWeil.archimedeanIntegrand
          (imagPartTest g).convolutionSquare y).re)
      (Set.Ioi (0 : ℝ)) := hI.re
  have hintergr :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        (C1SameOwnerWeil.archimedeanIntegrand g.convolutionSquare y).re) =
        (∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1SameOwnerWeil.archimedeanIntegrand
            (realPartTest g).convolutionSquare y).re) +
          ∫ y : ℝ in Set.Ioi (0 : ℝ),
            (C1SameOwnerWeil.archimedeanIntegrand
              (imagPartTest g).convolutionSquare y).re := by
    calc
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1SameOwnerWeil.archimedeanIntegrand g.convolutionSquare y).re) =
          ∫ y : ℝ in Set.Ioi (0 : ℝ),
            (C1SameOwnerWeil.archimedeanIntegrand
              (realPartTest g).convolutionSquare y).re +
              (C1SameOwnerWeil.archimedeanIntegrand
                (imagPartTest g).convolutionSquare y).re := by
        apply integral_congr_ae
        filter_upwards with y
        exact archimedeanIntegrand_re_split g y
      _ = _ := integral_add hRre hIre
  simp only [Complex.add_re]
  rw [hFsplit, hRsplit, hIsplit, hintergr]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [convolutionSquare_re_split g 0]
  ring

theorem gammaRArchProfileTerm_re_split
    (g : CompactLogTest) (n : ℕ) (y : ℝ) :
    (C1XiCenterTwoGamma.gammaRArchProfileTerm g.convolutionSquare n y).re =
      (C1XiCenterTwoGamma.gammaRArchProfileTerm
        (realPartTest g).convolutionSquare n y).re +
        (C1XiCenterTwoGamma.gammaRArchProfileTerm
          (imagPartTest g).convolutionSquare n y).re := by
  unfold C1XiCenterTwoGamma.gammaRArchProfileTerm
  have hfirst :
      Complex.exp (-((((2 * (n : ℝ) + 1 / 2 : ℝ) : ℂ) * (y : ℂ)))) =
        ((Real.exp (-(2 * (n : ℝ) + 1 / 2) * y) : ℝ) : ℂ) := by
    rw [show -((((2 * (n : ℝ) + 1 / 2 : ℝ) : ℂ) * (y : ℂ))) =
        ((-(2 * (n : ℝ) + 1 / 2) * y : ℝ) : ℂ) by
          push_cast
          ring,
      ← Complex.ofReal_exp]
  have hsecond :
      Complex.exp (-((((2 * (n : ℝ) + 1 : ℝ) : ℂ) * (y : ℂ)))) =
        ((Real.exp (-(2 * (n : ℝ) + 1) * y) : ℝ) : ℂ) := by
    rw [show -((((2 * (n : ℝ) + 1 : ℝ) : ℂ) * (y : ℂ))) =
        ((-(2 * (n : ℝ) + 1) * y : ℝ) : ℂ) by
          push_cast
          ring,
      ← Complex.ofReal_exp]
  rw [hfirst, hsecond]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [convolutionSquare_re_split g y,
    convolutionSquare_re_split g (-y), convolutionSquare_re_split g 0]
  rw [g.convolutionSquare_zero_im,
    (realPartTest g).convolutionSquare_zero_im,
    (imagPartTest g).convolutionSquare_zero_im]
  norm_num
  ring_nf

theorem gammaRArchProfileIntegral_re_split
    (g : CompactLogTest) (n : ℕ) :
    (C1XiCenterTwoGammaSummedKernel.gammaRArchProfileIntegral
      g.convolutionSquare n).re =
      (C1XiCenterTwoGammaSummedKernel.gammaRArchProfileIntegral
        (realPartTest g).convolutionSquare n).re +
        (C1XiCenterTwoGammaSummedKernel.gammaRArchProfileIntegral
          (imagPartTest g).convolutionSquare n).re := by
  unfold C1XiCenterTwoGammaSummedKernel.gammaRArchProfileIntegral
  have hF := C1XiCenterTwoGamma.integrableOn_gammaRArchProfileTerm_public
    g.convolutionSquare n
  have hR := C1XiCenterTwoGamma.integrableOn_gammaRArchProfileTerm_public
    (realPartTest g).convolutionSquare n
  have hI := C1XiCenterTwoGamma.integrableOn_gammaRArchProfileTerm_public
    (imagPartTest g).convolutionSquare n
  have hFr :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        C1XiCenterTwoGamma.gammaRArchProfileTerm
          g.convolutionSquare n y).re =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1XiCenterTwoGamma.gammaRArchProfileTerm
            g.convolutionSquare n y).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hF)
  have hRr : IntegrableOn
      (fun y : ℝ =>
        (C1XiCenterTwoGamma.gammaRArchProfileTerm
          (realPartTest g).convolutionSquare n y).re)
      (Set.Ioi (0 : ℝ)) := hR.re
  have hIr : IntegrableOn
      (fun y : ℝ =>
        (C1XiCenterTwoGamma.gammaRArchProfileTerm
          (imagPartTest g).convolutionSquare n y).re)
      (Set.Ioi (0 : ℝ)) := hI.re
  have hRsplit :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        C1XiCenterTwoGamma.gammaRArchProfileTerm
          (realPartTest g).convolutionSquare n y).re =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1XiCenterTwoGamma.gammaRArchProfileTerm
            (realPartTest g).convolutionSquare n y).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hR)
  have hIsplit :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        C1XiCenterTwoGamma.gammaRArchProfileTerm
          (imagPartTest g).convolutionSquare n y).re =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1XiCenterTwoGamma.gammaRArchProfileTerm
            (imagPartTest g).convolutionSquare n y).re := by
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hI)
  rw [hFr]
  calc
    (∫ y : ℝ in Set.Ioi (0 : ℝ),
        (C1XiCenterTwoGamma.gammaRArchProfileTerm
          g.convolutionSquare n y).re) =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (C1XiCenterTwoGamma.gammaRArchProfileTerm
            (realPartTest g).convolutionSquare n y).re +
            (C1XiCenterTwoGamma.gammaRArchProfileTerm
              (imagPartTest g).convolutionSquare n y).re := by
      apply integral_congr_ae
      filter_upwards with y
      exact gammaRArchProfileTerm_re_split g n y
    _ = _ := by
      rw [integral_add hRr hIr, hRsplit, hIsplit]

theorem laneRFinitePrefixQuadraticValue_split (g : CompactLogTest) :
    C1XiCenterTwoGammaConstrainedPrefix.laneRFinitePrefixQuadraticValue g =
      C1XiCenterTwoGammaConstrainedPrefix.laneRFinitePrefixQuadraticValue
        (realPartTest g) +
        C1XiCenterTwoGammaConstrainedPrefix.laneRFinitePrefixQuadraticValue
          (imagPartTest g) := by
  unfold C1XiCenterTwoGammaConstrainedPrefix.laneRFinitePrefixQuadraticValue
    C1XiCenterTwoGammaConstrainedPrefix.gammaRArchFinitePrefixValue
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [convolutionSquare_re_split g 0]
  have hprefix : ∀ n : ℕ,
      (C1XiCenterTwoGammaConstrainedPrefix.gammaRArchProfilePrefix
        g.convolutionSquare n).re =
        (C1XiCenterTwoGammaConstrainedPrefix.gammaRArchProfilePrefix
          (realPartTest g).convolutionSquare n).re +
          (C1XiCenterTwoGammaConstrainedPrefix.gammaRArchProfilePrefix
            (imagPartTest g).convolutionSquare n).re := by
    intro n
    unfold C1XiCenterTwoGammaConstrainedPrefix.gammaRArchProfilePrefix
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [Finset.sum_range_succ, Complex.add_re]
        rw [ih, gammaRArchProfileIntegral_re_split]
        ring
  rw [hprefix]
  ring

end
end C1XiCenterTwoGammaComplexSplit
end Source
end ConnesWeilRH
