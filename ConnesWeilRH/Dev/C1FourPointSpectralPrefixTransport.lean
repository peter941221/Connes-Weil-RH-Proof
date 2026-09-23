/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1TwoPointSpectralDecomposition

/-!
# Four-point spectral-prefix transport on the selected detector owner

The two-point annihilator controls the marked Hermitian pair but leaves the
other two points of the functional-equation orbit.  This file composes a
second two-point annihilator, still on the same `CompactLogTest` owner, so all
four orbit points are killed.  The resulting span with the already selected
detector has a nonpositive orbit contribution and preserves every non-orbit
square zero of the detector.

This is a finite-prefix reduction for the phase-balanced spectral route.  It
does not prove the detector gate sign or the high spectral-tail estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointSpectralPrefixTransport

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1SameOwnerWeil
open C1SpectralWeil
open C1TwoPointDifferentialAnnihilator
open C1TwoPointSpectralDecomposition
open scoped BigOperators

noncomputable section

/-- The four-point annihilator is the two-point annihilator at the marked
    Hermitian pair followed by the two-point annihilator at the remaining
    functional-equation pair. -/
def fullFunctionalEquationOrbitAnnihilator
    (g : CompactLogTest) (rho : ℂ) : CompactLogTest :=
  twoPointDerivativeAnnihilator
    (offlineZeroOrbitAnnihilator g rho)
    (star rho - 1 / 2) ((1 - rho) - 1 / 2)

theorem fullFunctionalEquationOrbitAnnihilator_support_subset_Icc
    (g : CompactLogTest) (rho : ℂ) {w : Real}
    (hsupport : Function.support (g.test : Real → ℂ) ⊆ Set.Icc (-w) w) :
    Function.support
        ((fullFunctionalEquationOrbitAnnihilator g rho).test : Real → ℂ) ⊆
      Set.Icc (-w) w := by
  unfold fullFunctionalEquationOrbitAnnihilator
  apply twoPointDerivativeAnnihilator_support_subset_Icc
  exact twoPointDerivativeAnnihilator_support_subset_Icc g
    (rho - 1 / 2) (1 - star rho - 1 / 2) hsupport

theorem laplaceAt_fullFunctionalEquationOrbitAnnihilator
    (g : CompactLogTest) (rho s : ℂ) :
    laplaceAt (fullFunctionalEquationOrbitAnnihilator g rho) s =
      (((1 - rho) - 1 / 2 - s) * (star rho - 1 / 2 - s) *
        ((1 - star rho) - 1 / 2 - s) * (rho - 1 / 2 - s)) *
        laplaceAt g s := by
  unfold fullFunctionalEquationOrbitAnnihilator
  rw [laplaceAt_twoPointDerivativeAnnihilator]
  unfold offlineZeroOrbitAnnihilator
  rw [laplaceAt_twoPointDerivativeAnnihilator]
  ring

theorem laplaceAt_fullOrbitSpanVector
    (g : CompactLogTest) (rho : ℂ) (lambda : Real) (s : ℂ) :
    laplaceAt
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho) g lambda) s =
      ((((1 - rho) - 1 / 2 - s) * (star rho - 1 / 2 - s) *
          ((1 - star rho) - 1 / 2 - s) * (rho - 1 / 2 - s)) -
        (lambda : ℂ)) * laplaceAt g s := by
  rw [laplaceAt_annihilatorDetectorSpanVector,
    laplaceAt_fullFunctionalEquationOrbitAnnihilator]
  ring

theorem fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple
    (g : CompactLogTest) (rho : ℂ)
    (hvanishes :
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet
      (fullFunctionalEquationOrbitAnnihilator g rho) := by
  unfold fullFunctionalEquationOrbitAnnihilator
  apply twoPointDerivativeAnnihilator_vanishesOn_cc20Triple
  exact twoPointDerivativeAnnihilator_vanishesOn_cc20Triple g
    (rho - 1 / 2) (1 - star rho - 1 / 2) hvanishes

theorem halfDensityShift_centered_negativeSourceOrbitValues
    (h : CompactLogTest) (rho : ℂ)
    (hraw :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
        laplaceAt h w.1 = negativeSourceOrbitValue rho w) :
    ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
      laplaceAt (halfDensityShift h) (w.1 - 1 / 2) =
        negativeSourceOrbitValue rho w := by
  intro w
  rw [laplaceAt_halfDensityShift]
  simpa using hraw w

theorem fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
    (g : CompactLogTest) (rho s : ℂ)
    (hzero : laplaceAt g s = 0) :
    laplaceAt (fullFunctionalEquationOrbitAnnihilator g rho) s = 0 := by
  unfold fullFunctionalEquationOrbitAnnihilator
  apply twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
  exact twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
    g (rho - 1 / 2) (1 - star rho - 1 / 2) s hzero

theorem fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_mem_orbit
    (g : CompactLogTest) (rho z : ℂ)
    (hz : z ∈ sourceFunctionalEquationOrbit rho) :
    laplaceAt (fullFunctionalEquationOrbitAnnihilator g rho) (z - 1 / 2) = 0 := by
  simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz | hz
  · subst z
    unfold fullFunctionalEquationOrbitAnnihilator
    exact twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
      (offlineZeroOrbitAnnihilator g rho)
      (star rho - 1 / 2) ((1 - rho) - 1 / 2) (rho - 1 / 2)
      (offlineZeroOrbitAnnihilator_laplaceAt_rho_sub_half g rho)
  · subst z
    unfold fullFunctionalEquationOrbitAnnihilator
    exact twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
      (offlineZeroOrbitAnnihilator g rho)
      (star rho - 1 / 2) ((1 - rho) - 1 / 2) (1 - star rho - 1 / 2)
      (offlineZeroOrbitAnnihilator_laplaceAt_one_sub_star_rho_sub_half g rho)
  · subst z
    unfold fullFunctionalEquationOrbitAnnihilator
    exact twoPointDerivativeAnnihilator_laplaceAt_z1
      (offlineZeroOrbitAnnihilator g rho)
      (star rho - 1 / 2) ((1 - rho) - 1 / 2)
  · subst z
    unfold fullFunctionalEquationOrbitAnnihilator
    exact twoPointDerivativeAnnihilator_laplaceAt_z2
      (offlineZeroOrbitAnnihilator g rho)
      (star rho - 1 / 2) ((1 - rho) - 1 / 2)

theorem fullOrbitSpanVector_convolutionSquare_laplaceAt_eq_zero_of_laplaceAt_eq_zero
    (g : CompactLogTest) (rho : ℂ) (lambda : Real) (s : ℂ)
    (hzero : laplaceAt g.convolutionSquare s = 0) :
    laplaceAt
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho) g lambda).convolutionSquare
        s = 0 := by
  have hfactor := laplaceAt_convolutionSquare g s
  rw [hzero] at hfactor
  rcases mul_eq_zero.mp hfactor.symm with hpartner | hvalue
  · have hu :
        laplaceAt (fullFunctionalEquationOrbitAnnihilator g rho) (-star s) = 0 :=
      fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
        g rho (-star s) (by simpa using hpartner)
    have hpartner' : laplaceAt g (-star s) = 0 := by
      simpa using hpartner
    have hv :
        laplaceAt
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho) g lambda)
          (-star s) = 0 := by
      rw [laplaceAt_annihilatorDetectorSpanVector, hu, hpartner']
      simp
    rw [laplaceAt_convolutionSquare, hv]
    simp
  · have hu :
        laplaceAt (fullFunctionalEquationOrbitAnnihilator g rho) s = 0 :=
      fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
        g rho s hvalue
    have hv :
        laplaceAt
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho) g lambda)
          s = 0 := by
      rw [laplaceAt_annihilatorDetectorSpanVector, hu, hvalue]
      simp
    rw [laplaceAt_convolutionSquare, hv]
    simp

theorem fullOrbitSpanVector_convolutionSquare_laplaceAt_rho_sub_half_eq_neg_sq_of_values
    (g : CompactLogTest) (rho : ℂ) (lambda : Real)
    (hg1 : laplaceAt g (rho - 1 / 2) = 1)
    (hg2 : laplaceAt g (1 - star rho - 1 / 2) = -1) :
    laplaceAt
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho) g lambda).convolutionSquare
        (rho - 1 / 2) = -((lambda : ℂ) ^ 2) := by
  have hu1 := fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_mem_orbit
    g rho rho (mem_sourceFunctionalEquationOrbit_rho rho)
  have hu2 := fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_mem_orbit
    g rho (1 - star rho) (mem_sourceFunctionalEquationOrbit_companion rho)
  have hcoord : -star (rho - 1 / 2) = 1 - star rho - 1 / 2 := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [laplaceAt_convolutionSquare, hcoord,
    laplaceAt_annihilatorDetectorSpanVector, hu2, hg2,
    laplaceAt_annihilatorDetectorSpanVector, hu1, hg1]
  simp [Complex.conj_ofReal]
  ring

theorem fullOrbitSpanVector_convolutionSquare_laplaceAt_eq_zero_or_neg_sq_of_mem_orbit
    (g : CompactLogTest) (rho : ℂ) (lambda : Real)
    (hoff : rho.re ≠ 1 / 2)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
        laplaceAt g (w.1 - 1 / 2) = negativeSourceOrbitValue rho w)
    (z : sourceNontrivialZeroSet)
    (hz : z.1 ∈ sourceFunctionalEquationOrbit rho) :
    laplaceAt
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho) g lambda).convolutionSquare
        (z.1 - 1 / 2) = 0 ∨
      laplaceAt
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho) g lambda).convolutionSquare
          (z.1 - 1 / 2) = -((lambda : ℂ) ^ 2) := by
  let v := annihilatorDetectorSpanVector
    (fullFunctionalEquationOrbitAnnihilator g rho) g lambda
  have hvalue (w : FiniteMellinNode (sourceFunctionalEquationOrbit rho)) :
      laplaceAt v (w.1 - 1 / 2) =
        -(lambda : ℂ) * negativeSourceOrbitValue rho w := by
    unfold v
    rw [laplaceAt_annihilatorDetectorSpanVector,
      fullFunctionalEquationOrbitAnnihilator_laplaceAt_eq_zero_of_mem_orbit
        g rho w.1 w.2, htarget w]
    ring
  have hpair (w : FiniteMellinNode (sourceFunctionalEquationOrbit rho)) :
      laplaceAt v.convolutionSquare (w.1 - 1 / 2) =
        star (laplaceAt v ((1 - star w.1) - 1 / 2)) *
          laplaceAt v (w.1 - 1 / 2) := by
    have hcoord : -star (w.1 - 1 / 2) = (1 - star w.1) - 1 / 2 := by
      apply Complex.ext <;> simp [Complex.star_def] <;> ring
    rw [laplaceAt_convolutionSquare, hcoord]
  have hsquare_rho :
      laplaceAt v.convolutionSquare (rho - 1 / 2) = -((lambda : ℂ) ^ 2) := by
    have hcomp :
        negativeSourceOrbitValue rho
          ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩ = -1 :=
      negativeSourceOrbitValue_companion rho hoff
    have hpairRho := hpair ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩
    have hpairRho' :
        laplaceAt v.convolutionSquare (rho - 1 / 2) =
          star (laplaceAt v ((1 - star rho) - 1 / 2)) *
            laplaceAt v (rho - 1 / 2) := by
      simpa only [Subtype.coe_mk] using hpairRho
    rw [hpairRho', hvalue ⟨1 - star rho,
      mem_sourceFunctionalEquationOrbit_companion rho⟩,
      hvalue ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩,
      hcomp, negativeSourceOrbitValue_rho]
    simp [Complex.conj_ofReal]
    ring
  have hsquare_companion :
      laplaceAt v.convolutionSquare ((1 - star rho) - 1 / 2) =
        -((lambda : ℂ) ^ 2) := by
    have hcomp :
        negativeSourceOrbitValue rho
          ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩ = -1 :=
      negativeSourceOrbitValue_companion rho hoff
    have hpairComp := hpair
      ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩
    have hpairComp' :
        laplaceAt v.convolutionSquare ((1 - star rho) - 1 / 2) =
          star (laplaceAt v (rho - 1 / 2)) *
            laplaceAt v ((1 - star rho) - 1 / 2) := by
      simpa [Complex.star_def] using hpairComp
    rw [hpairComp', hvalue ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩,
      hvalue ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩,
      negativeSourceOrbitValue_rho, hcomp]
    simp [Complex.conj_ofReal]
    ring
  simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz | hz
  · exact Or.inr (by simpa [v, hz] using hsquare_rho)
  · exact Or.inr (by simpa [v, hz] using hsquare_companion)
  · rw [hz]
    by_cases hnonreal : star rho ≠ rho
    · left
      have hstar :
          negativeSourceOrbitValue rho
            ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩ = 0 :=
        negativeSourceOrbitValue_star_of_ne rho hoff hnonreal
      have hone :
          negativeSourceOrbitValue rho
            ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩ = 0 :=
        negativeSourceOrbitValue_one_sub_of_ne rho hoff hnonreal
      have hmem :
          1 - star (star rho) ∈ sourceFunctionalEquationOrbit rho := by
        simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
          Finset.mem_singleton]
        simp
      have hcoord :
          1 - star (star rho) = 1 - rho := by simp
      rw [hpair ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩,
        hcoord, hvalue ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩,
        hvalue ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩,
        hstar, hone]
      simp
    · have hreal : star rho = rho := not_ne_iff.mp hnonreal
      exact Or.inr (by simpa [v, hz, hreal] using hsquare_rho)
  · rw [hz]
    by_cases hnonreal : star rho ≠ rho
    · left
      have hstar :
          negativeSourceOrbitValue rho
            ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩ = 0 :=
        negativeSourceOrbitValue_star_of_ne rho hoff hnonreal
      have hone :
          negativeSourceOrbitValue rho
            ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩ = 0 :=
        negativeSourceOrbitValue_one_sub_of_ne rho hoff hnonreal
      have hcoord :
          1 - star (1 - rho) = star rho := by simp
      rw [hpair ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩,
        hcoord, hvalue ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩,
        hvalue ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩,
        hstar, hone]
      simp
    · have hreal : star rho = rho := not_ne_iff.mp hnonreal
      have hcoord : 1 - rho = 1 - star rho := by rw [hreal]
      exact Or.inr (by simpa [v, hz, hreal, hcoord] using hsquare_companion)

theorem finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) (lambda : Real)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (hoff : rho.1.re ≠ 1 / 2)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt g (w.1 - 1 / 2) = negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt g.convolutionSquare (z.1 - 1 / 2) = 0) :
    (∑ z ∈ S,
      spectralTerm
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho.1) g lambda).convolutionSquare z).re ≤
      -(xiMultiplicity rho : Real) * lambda ^ 2 := by
  classical
  let v := annihilatorDetectorSpanVector
    (fullFunctionalEquationOrbitAnnihilator g rho.1) g lambda
  have hrealNegSq (m : Nat) :
      ((m : Complex) * (-((lambda : Complex) ^ 2))).re =
        -(m : Real) * lambda ^ 2 := by
    have hsquare : ((lambda : Complex) ^ 2).re = lambda ^ 2 := by
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    rw [Complex.mul_re]
    simp [hsquare]
  have hanchor :
      (spectralTerm v.convolutionSquare rho).re =
        -(xiMultiplicity rho : Real) * lambda ^ 2 := by
    have hg1 := htarget
      ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩
    have hg2 := htarget
      ⟨1 - star rho.1, mem_sourceFunctionalEquationOrbit_companion rho.1⟩
    rw [negativeSourceOrbitValue_rho] at hg1
    rw [negativeSourceOrbitValue_companion rho.1 hoff] at hg2
    have hsq :=
      fullOrbitSpanVector_convolutionSquare_laplaceAt_rho_sub_half_eq_neg_sq_of_values
        g rho.1 lambda hg1 hg2
    unfold spectralTerm centeredXiCoordinate v
    rw [hsq]
    exact hrealNegSq (xiMultiplicity rho)
  have hother (z : sourceNontrivialZeroSet) (hz : z ∈ S.erase rho) :
      (spectralTerm v.convolutionSquare z).re ≤ 0 := by
    by_cases horbit : z.1 ∈ sourceFunctionalEquationOrbit rho.1
    · rcases fullOrbitSpanVector_convolutionSquare_laplaceAt_eq_zero_or_neg_sq_of_mem_orbit
        g rho.1 lambda hoff htarget z horbit with hzero' | hneg
      · unfold spectralTerm centeredXiCoordinate v
        rw [hzero']
        norm_num
      · unfold spectralTerm centeredXiCoordinate v
        rw [hneg]
        rw [hrealNegSq]
        have hprod : 0 ≤ (xiMultiplicity z : Real) * lambda ^ 2 :=
          mul_nonneg (Nat.cast_nonneg _) (sq_nonneg lambda)
        nlinarith
    · have htransport := fullOrbitSpanVector_convolutionSquare_laplaceAt_eq_zero_of_laplaceAt_eq_zero
        g rho.1 lambda (z.1 - 1 / 2) (hzero z (Finset.mem_of_mem_erase hz) horbit)
      unfold spectralTerm centeredXiCoordinate v
      rw [htransport]
      norm_num
  have hrest :
      ∑ z ∈ S.erase rho, (spectralTerm v.convolutionSquare z).re ≤ 0 := by
    exact Finset.sum_nonpos (fun z hz => hother z hz)
  have hrestRe :
      (∑ z ∈ S.erase rho, spectralTerm v.convolutionSquare z).re =
        ∑ z ∈ S.erase rho, (spectralTerm v.convolutionSquare z).re := by
    simp
  have hsplit := Finset.sum_erase_add
    (s := S) (f := fun z : sourceNontrivialZeroSet => spectralTerm v.convolutionSquare z)
    (a := rho) hrho
  calc
    (∑ z ∈ S, spectralTerm v.convolutionSquare z).re =
        ((∑ z ∈ S.erase rho, spectralTerm v.convolutionSquare z) +
          spectralTerm v.convolutionSquare rho).re := by
      rw [hsplit]
    _ = (∑ z ∈ S.erase rho, (spectralTerm v.convolutionSquare z).re) +
          (spectralTerm v.convolutionSquare rho).re := by
      rw [Complex.add_re, hrestRe]
    _ ≤ -(xiMultiplicity rho : Real) * lambda ^ 2 := by
      rw [hanchor]
      linarith

end
end C1FourPointSpectralPrefixTransport
end Source
end ConnesWeilRH
