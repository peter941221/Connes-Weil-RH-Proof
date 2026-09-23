/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1TwoPointDifferentialAnnihilator
import ConnesWeilRH.Dev.C1PinnedOrbitExit
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1GateMatrixRepresentation
import ConnesWeilRH.Dev.C1T2Assembly
import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
import Mathlib.Analysis.Complex.Basic

/-!
# Two-Point Spectral Decomposition: Orbit Pairing on the Annihilator-Detector Span

This module formalizes the exact spectral orbit pairing of the linear combination:
`v(lambda) = spanObj ![u_a, g] ![1, -lambda]`
where:
- `u_a` is the two-point differential annihilator of `narrowArchRoot` at `rho - 1/2`
  and `1 - star rho - 1/2`;
- `g` is the pinned Yoshida detector with target values `1` and `-1` on the orbit.

Key Theorems:
1. `laplaceAt (v(lambda)) (rho - 1/2) = -lambda`;
2. `laplaceAt (v(lambda)) (1 - star rho - 1/2) = lambda`;
3. The paired product `star (laplaceAt v(lambda) (1 - star rho - 1/2)) * laplaceAt v(lambda) (rho - 1/2) = -lambda^2`;
4. Preserved triple vanishing on `{0, 1/2, 1}` and support containment in `(-B, B)`.

Consumer: Contradiction between the nonpositive spectral orbit and the nonnegative Weil energy.
-/

namespace ConnesWeilRH
namespace Source
namespace C1TwoPointSpectralDecomposition

open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1TwoPointDifferentialAnnihilator
open C1PinnedOrbitExit
open C1G8R0OrbitGeometry
open C1GateMatrixRepresentation
open C1T2Assembly
open C1LaneRNarrowArch
open C1HealthyYoshidaDetector
open C1SameOwnerWeil
open Set

noncomputable section

/-- The canonical annihilator-detector span vector `v(lambda) = u_a - lambda * g`. -/
def annihilatorDetectorSpanVector
    (u_a g : CompactLogTest) (lambda : Real) : CompactLogTest :=
  spanObj ![u_a, g] ![(1 : Real), -lambda]

/-- Linearity of Laplace evaluation on the annihilator-detector span vector. -/
theorem laplaceAt_annihilatorDetectorSpanVector
    (u_a g : CompactLogTest) (lambda : Real) (s : ℂ) :
    laplaceAt (annihilatorDetectorSpanVector u_a g lambda) s =
      laplaceAt u_a s - (lambda : ℂ) * laplaceAt g s := by
  unfold annihilatorDetectorSpanVector
  rw [laplaceAt_spanObj_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Complex.ofReal_one, one_mul,
    Matrix.cons_val_one, Matrix.head_cons, Complex.ofReal_neg]
  ring

/-- Exact Laplace evaluation at `rho - 1/2`: because `u_a` vanishes and `g` evaluates to `1`,
    the span vector evaluates to `-lambda`. -/
theorem laplaceAt_annihilatorDetectorSpanVector_at_rho_sub_half
    (u_a g : CompactLogTest) (lambda : Real) (rho : ℂ)
    (hu : laplaceAt u_a (rho - 1 / 2) = 0)
    (hg : laplaceAt g (rho - 1 / 2) = 1) :
    laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (rho - 1 / 2) = -(lambda : ℂ) := by
  rw [laplaceAt_annihilatorDetectorSpanVector, hu, hg]
  ring

/-- Exact Laplace evaluation at `1 - star rho - 1/2`: because `u_a` vanishes and `g` evaluates to `-1`,
    the span vector evaluates to `+lambda`. -/
theorem laplaceAt_annihilatorDetectorSpanVector_at_one_sub_star_rho_sub_half
    (u_a g : CompactLogTest) (lambda : Real) (rho : ℂ)
    (hu : laplaceAt u_a (1 - star rho - 1 / 2) = 0)
    (hg : laplaceAt g (1 - star rho - 1 / 2) = -1) :
    laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (1 - star rho - 1 / 2) = (lambda : ℂ) := by
  rw [laplaceAt_annihilatorDetectorSpanVector, hu, hg]
  ring

/-- The paired product of the span vector at the off-line zero orbit is strictly nonpositive:
    `star (laplaceAt v (1 - star rho - 1/2)) * laplaceAt v (rho - 1/2) = -(lambda^2)`. -/
theorem pairedProduct_annihilatorDetectorSpanVector_eq_neg_sq
    (u_a g : CompactLogTest) (lambda : Real) (rho : ℂ)
    (hu1 : laplaceAt u_a (rho - 1 / 2) = 0)
    (hg1 : laplaceAt g (rho - 1 / 2) = 1)
    (hu2 : laplaceAt u_a (1 - star rho - 1 / 2) = 0)
    (hg2 : laplaceAt g (1 - star rho - 1 / 2) = -1) :
    star (laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (1 - star rho - 1 / 2)) *
        laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (rho - 1 / 2) =
      -((lambda : ℂ) ^ 2) := by
  have h1 := laplaceAt_annihilatorDetectorSpanVector_at_rho_sub_half u_a g lambda rho hu1 hg1
  have h2 := laplaceAt_annihilatorDetectorSpanVector_at_one_sub_star_rho_sub_half u_a g lambda rho hu2 hg2
  rw [h1, h2]
  have hstar : star (lambda : ℂ) = (lambda : ℂ) := Complex.conj_ofReal lambda
  rw [hstar]
  ring

/-- Triple vanishing on `{0, 1/2, 1}` is strictly preserved by the annihilator-detector span vector. -/
theorem annihilatorDetectorSpanVector_vanishesOn_cc20Triple
    (u_a g : CompactLogTest) (lambda : Real)
    (hu : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet u_a)
    (hg : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (annihilatorDetectorSpanVector u_a g lambda) := by
  unfold annihilatorDetectorSpanVector
  exact vanishesOn_cc20Triple_spanObj_two u_a g 1 (-lambda) hu hg

/-- Support containment: If `u_a` and `g` are supported in `(-B, B)`, then their span vector
    is supported in `(-B, B)`. -/
theorem annihilatorDetectorSpanVector_support_subset_Ioo
    (u_a g : CompactLogTest) (lambda : Real) (B : Real)
    (hu : Function.support u_a.test ⊆ Set.Ioo (-B) B)
    (hg : Function.support g.test ⊆ Set.Ioo (-B) B) :
    Function.support (annihilatorDetectorSpanVector u_a g lambda).test ⊆ Set.Ioo (-B) B := by
  unfold annihilatorDetectorSpanVector
  apply spanObj_support
  intro i
  fin_cases i
  · simpa using hu
  · simpa using hg

end
end C1TwoPointSpectralDecomposition
end Source
end ConnesWeilRH
