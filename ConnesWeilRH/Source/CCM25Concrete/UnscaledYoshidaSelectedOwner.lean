/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaFullProduct
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Selected owner for the unscaled Yoshida assembly

This module keeps the support-growing Yoshida source factor tied to the
existing selected convolution square and whole-line finite-prime crossing
operator.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace UnscaledYoshidaSelectedOwner

open MeasureTheory
open CC20YoshidaNearZeros
open CC20YoshidaConvolution.CompactLogTest
open CompactLogConvolution
open ConnesWeilRH.Source.CC20Concrete
open SelectedCrossingOperatorBridge
open scoped ComplexConjugate ContDiff InnerProductSpace

/-- Convert the source Mellin coordinate `s` to Burnol's centered log
coordinate `u = s - 1/2`. Multiplication by `exp(x/2)` preserves support. -/
noncomputable def halfDensityShift (f : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x =>
    Complex.exp ((1 / 2 : ℂ) * (x : ℂ)) * f.test x
  have hcompact : HasCompactSupport raw := f.compactSupport.mul_left
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    have hlinear : ContDiff ℝ ∞
        (fun x : ℝ => (1 / 2 : ℂ) * (x : ℂ)) :=
      contDiff_const.mul Complex.ofRealCLM.contDiff
    exact hlinear.cexp.mul (f.test.smooth ⊤)
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem halfDensityShift_apply (f : CompactLogTest) (x : ℝ) :
    (halfDensityShift f).test x =
      Complex.exp ((1 / 2 : ℂ) * (x : ℂ)) * f.test x :=
  rfl

/-- The half-density multiplier translates the bilateral Laplace variable by
`1/2`. This is the coordinate change in Burnol's selected explicit formula. -/
theorem laplaceAt_halfDensityShift (f : CompactLogTest) (s : ℂ) :
    laplaceAt (halfDensityShift f) s = laplaceAt f (s + 1 / 2) := by
  unfold laplaceAt
  apply integral_congr_ae
  filter_upwards with x
  simp only [exponentialWeight_apply, halfDensityShift_apply]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem halfDensityShift_support_subset
    (f : CompactLogTest) {a c : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo a c) :
    Function.support (halfDensityShift f).test ⊆ Set.Ioo a c := by
  intro x hx
  apply hsupport
  rw [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  simp [hzero]

theorem centered_add_half (rho : ℂ) :
    rho - 1 / 2 + 1 / 2 = rho := by
  ring

theorem neg_star_centered_add_half (rho : ℂ) :
    -star (rho - 1 / 2) + 1 / 2 = 1 - star rho := by
  simp
  ring

/-- The centered functional-equation/conjugation orbit, obtained by applying
the half-density translation to the source orbit.  `Finset.image` preserves
any genuine orbit collision. -/
noncomputable def centeredFunctionalEquationOrbit (rho : ℂ) : Finset ℂ :=
  (sourceFunctionalEquationOrbit rho).image fun z => z - 1 / 2

/-- The existing selected square owner applied to the half-density shift of
one unscaled Yoshida source factor. The shift is required before the source
Mellin point `rho` becomes the selected spectral point `rho - 1/2`. -/
noncomputable def selectedOwner
    (base correction : CompactLogTest) (n : ℕ) :
    SelectedWeilSquare.SelectedWeilSquareOwner :=
  SelectedWeilSquare.SelectedWeilSquareOwner.ofCompactLogTest
    (halfDensityShift
      ((convolutionIterate base n).convolution correction))

@[simp] theorem selectedOwner_sourceTest
    (base correction : CompactLogTest) (n : ℕ) :
    (selectedOwner base correction n).sourceTest =
      halfDensityShift
        ((convolutionIterate base n).convolution correction) :=
  rfl

@[simp] theorem selectedOwner_convolutionSquare
    (base correction : CompactLogTest) (n : ℕ) :
    (selectedOwner base correction n).convolutionSquare =
      (halfDensityShift
        ((convolutionIterate base n).convolution correction)).convolutionSquare :=
  rfl

/-- Normalizing the source point and its functional-equation companion
normalizes the actual selected convolution square at `rho - 1/2`. -/
theorem selectedOwner_laplaceAt_convolutionSquare_eq_one
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = 1) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (rho - 1 / 2) = 1 := by
  rw [selectedOwner_convolutionSquare, CompactLogTest.convolutionSquare,
    laplaceAt_convolution, laplaceAt_involution,
    laplaceAt_halfDensityShift, laplaceAt_halfDensityShift,
    centered_add_half, neg_star_centered_add_half, hcomp, hrho]
  simp

/-- The selected square at the centered point `z - 1/2` is exactly the
Hermitian product of the two source-Mellin values at `z` and
`1 - conj(z)`. -/
theorem selectedOwner_laplaceAt_convolutionSquare_centered
    (base correction : CompactLogTest) (n : ℕ) (z : ℂ) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2) =
      star (laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star z)) *
        laplaceAt ((convolutionIterate base n).convolution correction) z := by
  rw [selectedOwner_convolutionSquare, CompactLogTest.convolutionSquare,
    laplaceAt_convolution, laplaceAt_involution,
    laplaceAt_halfDensityShift, laplaceAt_halfDensityShift,
    centered_add_half, neg_star_centered_add_half]

/-- The prescribed values `1` and `-1` on the source functional-equation
pair give two selected-square values equal to `-1`. -/
theorem selectedOwner_negativeHermitianPair_sum_eq_neg_two
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = -1) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
          (rho - 1 / 2) +
        laplaceAt (selectedOwner base correction n).convolutionSquare
          ((1 - star rho) - 1 / 2) = -2 := by
  rw [selectedOwner_laplaceAt_convolutionSquare_centered,
    selectedOwner_laplaceAt_convolutionSquare_centered,
    hrho, hcomp]
  simp [hrho]
  norm_num

/-- In the nonreal four-point case, the two remaining source values vanish,
so the complete ordered centered-orbit contribution is exactly `-2`. -/
theorem selectedOwner_negativeFourPointOrbit_sum_eq_neg_two
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = -1)
    (hstar :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (star rho) = 0)
    (honeSub :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - rho) = 0) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
          (rho - 1 / 2) +
        laplaceAt (selectedOwner base correction n).convolutionSquare
          ((1 - star rho) - 1 / 2) +
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (star rho - 1 / 2) +
        laplaceAt (selectedOwner base correction n).convolutionSquare
          ((1 - rho) - 1 / 2) = -2 := by
  have hpair := selectedOwner_negativeHermitianPair_sum_eq_neg_two
    base correction n rho hrho hcomp
  have hstarSquare :
      laplaceAt (selectedOwner base correction n).convolutionSquare
          (star rho - 1 / 2) = 0 :=
    by
      rw [selectedOwner_laplaceAt_convolutionSquare_centered, hstar]
      simp
  have honeSubSquare :
      laplaceAt (selectedOwner base correction n).convolutionSquare
          ((1 - rho) - 1 / 2) = 0 :=
    by
      rw [selectedOwner_laplaceAt_convolutionSquare_centered, honeSub]
      simp
  rw [hstarSquare, honeSubSquare]
  simpa using hpair

/-- When the off-line orbit is genuinely nonreal, the ordered four-term
identity is the sum over the actual centered orbit `Finset`; no duplicate
point is counted by notation. -/
theorem selectedOwner_centeredOrbit_sum_eq_neg_two_of_nonreal
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (hoff : rho.re ≠ 1 / 2) (hnonreal : star rho ≠ rho)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = -1)
    (hstar :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (star rho) = 0)
    (honeSub :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - rho) = 0) :
    ∑ u ∈ centeredFunctionalEquationOrbit rho,
        laplaceAt (selectedOwner base correction n).convolutionSquare u = -2 := by
  have hab : rho ≠ 1 - star rho :=
    ne_one_sub_star_of_re_ne_half rho hoff
  have hac : rho ≠ star rho := hnonreal.symm
  have had : rho ≠ 1 - rho :=
    ne_one_sub_self_of_re_ne_half rho hoff
  have hbc : 1 - star rho ≠ star rho :=
    (star_ne_one_sub_star_of_re_ne_half rho hoff).symm
  have hbd : 1 - star rho ≠ 1 - rho := by
    intro h
    apply hnonreal
    exact sub_right_inj.mp h
  have hcd : star rho ≠ 1 - rho :=
    star_ne_one_sub_self_of_re_ne_half rho hoff
  have hfour := selectedOwner_negativeFourPointOrbit_sum_eq_neg_two
    base correction n rho hrho hcomp hstar honeSub
  rw [centeredFunctionalEquationOrbit, Finset.sum_image]
  · rw [sourceFunctionalEquationOrbit,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hac, had⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hbc, hbd⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact hcd),
      Finset.sum_singleton]
    simpa [add_assoc] using hfour
  · intro a _ b _ h
    exact sub_left_inj.mp h

/-- The adaptive source-orbit values give centered-orbit sum `-2` for every
off-line point.  If conjugation fixes `rho`, the `Finset` collapses to the two
functional-equation points; otherwise the preceding four-point theorem
applies. -/
theorem selectedOwner_centeredOrbit_sum_eq_neg_two
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (hoff : rho.re ≠ 1 / 2)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = -1)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho w) :
    ∑ u ∈ centeredFunctionalEquationOrbit rho,
        laplaceAt (selectedOwner base correction n).convolutionSquare u = -2 := by
  by_cases hnonreal : star rho ≠ rho
  · have hstar :
        laplaceAt ((convolutionIterate base n).convolution correction)
            (star rho) = 0 :=
      calc
        laplaceAt ((convolutionIterate base n).convolution correction)
            (star rho) =
            negativeSourceOrbitValue rho
              ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩ :=
          htargets ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩
        _ = 0 := negativeSourceOrbitValue_star_of_ne rho hoff hnonreal
    have honeSub :
        laplaceAt ((convolutionIterate base n).convolution correction)
            (1 - rho) = 0 :=
      calc
        laplaceAt ((convolutionIterate base n).convolution correction)
            (1 - rho) =
            negativeSourceOrbitValue rho
              ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩ :=
          htargets ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩
        _ = 0 := negativeSourceOrbitValue_one_sub_of_ne rho hoff hnonreal
    exact selectedOwner_centeredOrbit_sum_eq_neg_two_of_nonreal
      base correction n rho hoff hnonreal hrho hcomp hstar honeSub
  · have hreal : star rho = rho := not_ne_iff.mp hnonreal
    have had : rho ∉ ({1 - rho} : Finset ℂ) := by
      simpa only [Finset.mem_singleton] using
        ne_one_sub_self_of_re_ne_half rho hoff
    have hpair := selectedOwner_negativeHermitianPair_sum_eq_neg_two
      base correction n rho hrho hcomp
    have hcollapse :
        ({rho, 1 - rho, rho, 1 - rho} : Finset ℂ) = {rho, 1 - rho} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [centeredFunctionalEquationOrbit, Finset.sum_image]
    · rw [sourceFunctionalEquationOrbit, hreal]
      rw [hcollapse]
      rw [Finset.sum_insert had, Finset.sum_singleton]
      simpa [hreal] using hpair
    · intro a _ b _ h
      exact sub_left_inj.mp h

/-- A zero of the assembled source factor is a zero of the selected
convolution square at the corresponding centered node. -/
theorem selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
    (base correction : CompactLogTest) (n : ℕ) (z : ℂ)
    (hz :
      laplaceAt ((convolutionIterate base n).convolution correction) z = 0) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2) = 0 := by
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, hz]
  simp

/-- Two source-factor distance bounds multiply into a fourth-order bound for
the actual selected convolution square. -/
theorem selectedOwner_convolutionSquare_doubleDistance_bound_lt
    (base correction : CompactLogTest) (n : ℕ) (rho z : ℂ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hz : ‖z - rho‖ ^ 2 *
        ‖laplaceAt ((convolutionIterate base n).convolution correction) z‖ <
      epsilon)
    (hcomp : ‖(1 - star z) - rho‖ ^ 2 *
        ‖laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - star z)‖ < epsilon) :
    ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
        ‖laplaceAt (selectedOwner base correction n).convolutionSquare
          (z - 1 / 2)‖ < epsilon ^ 2 := by
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, norm_mul, norm_star]
  calc
    ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
          (‖laplaceAt ((convolutionIterate base n).convolution correction)
              (1 - star z)‖ *
            ‖laplaceAt ((convolutionIterate base n).convolution correction) z‖) =
        (‖z - rho‖ ^ 2 *
          ‖laplaceAt ((convolutionIterate base n).convolution correction) z‖) *
        (‖(1 - star z) - rho‖ ^ 2 *
          ‖laplaceAt ((convolutionIterate base n).convolution correction)
            (1 - star z)‖) := by ring
    _ < epsilon * epsilon := by
      by_cases hzero :
          ‖(1 - star z) - rho‖ ^ 2 *
              ‖laplaceAt ((convolutionIterate base n).convolution correction)
                (1 - star z)‖ = 0
      · rw [hzero, mul_zero]
        positivity
      · apply mul_lt_mul hz hcomp.le
        · exact lt_of_le_of_ne
            (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (Ne.symm hzero)
        · exact hepsilon.le
    _ = epsilon ^ 2 := by ring

/-- Transport a raw source-factor distance bound through the half-density
translation without changing its threshold or support geometry. -/
theorem selectedOwner_centered_source_distance_bound_lt
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (T epsilon : ℝ)
    (htail : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt
              ((convolutionIterate base n).convolution correction) z‖ <
          epsilon) :
    ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt (selectedOwner base correction n).sourceTest
              (z - 1 / 2)‖ < epsilon := by
  intro z hz hTz hone hrhoHeight
  rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
    centered_add_half]
  exact htail z hz hTz hone hrhoHeight

/-- Apply the same raw tail at `z` and `1-conj(z)` to obtain the fourth-order
tail of the actual selected convolution square. -/
theorem selectedOwner_convolutionSquare_tail_of_source_tail
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (T epsilon : ℝ) (hepsilon : 0 < epsilon)
    (htail : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt
              ((convolutionIterate base n).convolution correction) z‖ <
          epsilon) :
    ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
            ‖laplaceAt
              (selectedOwner base correction n).convolutionSquare
              (z - 1 / 2)‖ < epsilon ^ 2 := by
  intro z hz hTz hone hrhoHeight
  have hcompRe : (1 - star z).re ∈ Set.Icc (0 : ℝ) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    constructor <;> linarith [hz.1, hz.2]
  have hcompIm : (1 - star z).im = z.im := by
    simp
  have htailComp :
      ‖(1 - star z) - rho‖ ^ 2 *
          ‖laplaceAt ((convolutionIterate base n).convolution correction)
            (1 - star z)‖ < epsilon := by
    apply htail (1 - star z) hcompRe
    · simpa only [hcompIm] using hTz
    · simpa only [hcompIm] using hone
    · simpa only [hcompIm] using hrhoHeight
  exact selectedOwner_convolutionSquare_doubleDistance_bound_lt
    base correction n rho z epsilon hepsilon
    (htail z hz hTz hone hrhoHeight) htailComp

theorem selectedOwner_sourceTest_support_subset_Icc
    (base correction : CompactLogTest) (n : ℕ) {a c : ℝ}
    (hsupport : Function.support
        ((convolutionIterate base n).convolution correction).test ⊆
      Set.Ioo a c) :
    Function.support (selectedOwner base correction n).sourceTest.test ⊆
      Set.Icc a c := by
  intro x hx
  have hshifted : x ∈ Function.support
      ((convolutionIterate base n).convolution correction).test := by
    rw [Function.mem_support] at hx ⊢
    intro hzero
    apply hx
    simp [hzero]
  have hbounds := hsupport hshifted
  exact ⟨hbounds.1.le, hbounds.2.le⟩

/-- The whole-line finite-prime operator built from the assembled Yoshida
source factor is compact whenever the existing per-prime basis witnesses are
supplied. -/
theorem operatorSum_isCompactOperator
    (base correction : CompactLogTest) (n : ℕ)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hsupport : Function.support
        ((convolutionIterate base n).convolution correction).test ⊆
      Set.Ioo a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    IsCompactOperator
      (eulerLogWeightedGlobalPairTraceOperatorSum
        (selectedOwner base correction n) terms) := by
  exact eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator
    (selectedOwner base correction n) a c terms hprime
    (selectedOwner_sourceTest_support_subset_Icc
      base correction n hsupport) globalBasis basisData

theorem operatorSum_isSelfAdjoint
    (base correction : CompactLogTest) (n : ℕ)
    (terms : Finset (ℕ × ℕ)) :
    IsSelfAdjoint
      (eulerLogWeightedGlobalPairTraceOperatorSum
        (selectedOwner base correction n) terms) :=
  eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint
    (selectedOwner base correction n) terms

/-- The compact operator trace and the selected finite-prime sum use the same
assembled Yoshida source factor and the same selected square owner. -/
theorem ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum
    (base correction : CompactLogTest) (n : ℕ)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupport : Function.support
        ((convolutionIterate base n).convolution correction).test ⊆
      Set.Ioo a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (eulerLogWeightedGlobalPairTraceOperatorSum
          (selectedOwner base correction n) terms) =
      ∑ pm ∈ terms,
        (selectedOwner base correction n).finitePrimeTerm (pm.1 ^ pm.2) := by
  exact
    ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
      (selectedOwner base correction n) a c terms hprime hnonzero
      (selectedOwner_sourceTest_support_subset_Icc
        base correction n hsupport) globalBasis basisData

/-- The fixed-threshold source-orbit construction produces an actual selected
owner whose convolution square detects the centered point `rho - 1/2`,
cancels the selected non-target source zeros at their centered points, and
retains the same unscaled far-tail estimate. -/
theorem exists_fixedWindows_nearbyZero_selectedOwner
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (routeNodes : Finset ℂ)
    {baseLower baseUpper lower upper : ℝ}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ base : CompactLogTest, ∃ T : ℝ,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      0 ≤ T ∧
      ∀ R : ℝ, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : ℝ, ∃ n : ℕ,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support (selectedOwner base correction n).sourceTest.test ⊆
            Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
              (((n + 1 : ℕ) : ℝ) * baseUpper + upper) ∧
          laplaceAt (selectedOwner base correction n).sourceTest
              (rho - 1 / 2) = 1 ∧
          laplaceAt (selectedOwner base correction n).sourceTest
              (-star (rho - 1 / 2)) = 1 ∧
          laplaceAt (selectedOwner base correction n).convolutionSquare
              (rho - 1 / 2) = 1 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ∉ ({rho, 1 - star rho} : Finset ℂ) →
              laplaceAt (selectedOwner base correction n).convolutionSquare
                (z.1 - 1 / 2) = 0) ∧
          0 ≤ C ∧
          (∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt (selectedOwner base correction n).sourceTest
                    (z - 1 / 2)‖ < epsilon) ∧
          ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
                  ‖laplaceAt
                    (selectedOwner base correction n).convolutionSquare
                    (z - 1 / 2)‖ < epsilon ^ 2 := by
  obtain ⟨base, T, hbaseSupport, _hbaseRho, _hbaseComp, hT, hfamily⟩ :=
    exists_fixedWindows_nearbyZero_unscaled_sourceOrbit_assembly
      rho hrho routeNodes hbaseLower hbaseUpper hlower hupper epsilon hepsilon
  refine ⟨base, T, hbaseSupport, hT, ?_⟩
  intro R hR
  obtain ⟨correction, C, n, hcorrectionSupport, hsourceSupport,
      hsourceRho, hsourceComp, hsourceZeros, hC, htail⟩ :=
    hfamily R hR
  have hselectedSupport :
      Function.support (selectedOwner base correction n).sourceTest.test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
          (((n + 1 : ℕ) : ℝ) * baseUpper + upper) := by
    simpa only [selectedOwner_sourceTest] using
      halfDensityShift_support_subset
        ((convolutionIterate base n).convolution correction) hsourceSupport
  have hcenterRho :
      laplaceAt (selectedOwner base correction n).sourceTest
          (rho - 1 / 2) = 1 := by
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      centered_add_half]
    exact hsourceRho
  have hcenterComp :
      laplaceAt (selectedOwner base correction n).sourceTest
          (-star (rho - 1 / 2)) = 1 := by
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      neg_star_centered_add_half]
    exact hsourceComp
  have hsquareRho :
      laplaceAt (selectedOwner base correction n).convolutionSquare
          (rho - 1 / 2) = 1 :=
    selectedOwner_laplaceAt_convolutionSquare_eq_one
      base correction n rho hsourceRho hsourceComp
  have hsquareZeros :
      ∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        z.1 ∉ ({rho, 1 - star rho} : Finset ℂ) →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (z.1 - 1 / 2) = 0 := by
    intro z hz
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n z.1 (hsourceZeros z hz)
  have hcenteredTail :
      ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
        T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
          ‖z - rho‖ ^ 2 *
              ‖laplaceAt (selectedOwner base correction n).sourceTest
                (z - 1 / 2)‖ < epsilon :=
    selectedOwner_centered_source_distance_bound_lt
      base correction n rho T epsilon htail
  have hsquareTail :
      ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
        T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
          ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
              ‖laplaceAt
                (selectedOwner base correction n).convolutionSquare
                (z - 1 / 2)‖ < epsilon ^ 2 :=
    selectedOwner_convolutionSquare_tail_of_source_tail
      base correction n rho T epsilon hepsilon htail
  exact ⟨correction, C, n, hcorrectionSupport, hselectedSupport,
    hcenterRho, hcenterComp, hsquareRho, hsquareZeros, hC,
    hcenteredTail, hsquareTail⟩

/-- A nonreal off-line source orbit produces one selected owner with the full
`1,-1,0,0` source pattern, actual centered-orbit square sum `-2`, cancellation
of every other selected source node, and the same fourth-order square tail.
The theorem changes the detector sign; it does not assert the finite-S
semilocal remainder inequality. -/
theorem exists_fixedWindows_nearbyZero_negativeFourPointOrbit_selectedOwner
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hoff : rho.re ≠ 1 / 2) (hnonreal : star rho ≠ rho)
    (routeNodes : Finset ℂ)
    {baseLower baseUpper lower upper : ℝ}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ base : CompactLogTest, ∃ T : ℝ,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      0 ≤ T ∧
      ∀ R : ℝ, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : ℝ, ∃ n : ℕ,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support (selectedOwner base correction n).sourceTest.test ⊆
            Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
              (((n + 1 : ℕ) : ℝ) * baseUpper + upper) ∧
          laplaceAt (selectedOwner base correction n).sourceTest
              (rho - 1 / 2) = 1 ∧
          laplaceAt (selectedOwner base correction n).sourceTest
              ((1 - star rho) - 1 / 2) = -1 ∧
          laplaceAt (selectedOwner base correction n).sourceTest
              (star rho - 1 / 2) = 0 ∧
          laplaceAt (selectedOwner base correction n).sourceTest
              ((1 - rho) - 1 / 2) = 0 ∧
          (∑ u ∈ centeredFunctionalEquationOrbit rho,
            laplaceAt (selectedOwner base correction n).convolutionSquare u) =
              -2 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ∉ sourceFunctionalEquationOrbit rho →
              laplaceAt (selectedOwner base correction n).convolutionSquare
                (z.1 - 1 / 2) = 0) ∧
          0 ≤ C ∧
          (∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt (selectedOwner base correction n).sourceTest
                    (z - 1 / 2)‖ < epsilon) ∧
          ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
                  ‖laplaceAt
                    (selectedOwner base correction n).convolutionSquare
                    (z - 1 / 2)‖ < epsilon ^ 2 := by
  obtain ⟨base, T, hbaseSupport, _hbaseTargets, hT, hfamily⟩ :=
    exists_fixedWindows_nearbyZero_unscaled_negativeSourceOrbit_assembly
      rho hrho hoff routeNodes hbaseLower hbaseUpper hlower hupper
      epsilon hepsilon
  refine ⟨base, T, hbaseSupport, hT, ?_⟩
  intro R hR
  obtain ⟨correction, C, n, hcorrectionSupport, hsourceSupport,
      hsourceRho, hsourceComp, hsourceTargets, hsourceZeros, hC, htail⟩ :=
    hfamily R hR
  have hsourceStar :
      laplaceAt ((convolutionIterate base n).convolution correction)
          (star rho) = 0 :=
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (star rho) =
          negativeSourceOrbitValue rho
            ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩ :=
        hsourceTargets
          ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩
      _ = 0 := negativeSourceOrbitValue_star_of_ne rho hoff hnonreal
  have hsourceOneSub :
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - rho) = 0 :=
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - rho) =
          negativeSourceOrbitValue rho
            ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩ :=
        hsourceTargets
          ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩
      _ = 0 := negativeSourceOrbitValue_one_sub_of_ne rho hoff hnonreal
  have hselectedSupport :
      Function.support (selectedOwner base correction n).sourceTest.test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
          (((n + 1 : ℕ) : ℝ) * baseUpper + upper) := by
    simpa only [selectedOwner_sourceTest] using
      halfDensityShift_support_subset
        ((convolutionIterate base n).convolution correction) hsourceSupport
  have hcenterRho :
      laplaceAt (selectedOwner base correction n).sourceTest
          (rho - 1 / 2) = 1 := by
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      centered_add_half]
    exact hsourceRho
  have hcenterComp :
      laplaceAt (selectedOwner base correction n).sourceTest
          ((1 - star rho) - 1 / 2) = -1 := by
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      centered_add_half]
    exact hsourceComp
  have hcenterStar :
      laplaceAt (selectedOwner base correction n).sourceTest
          (star rho - 1 / 2) = 0 := by
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      centered_add_half]
    exact hsourceStar
  have hcenterOneSub :
      laplaceAt (selectedOwner base correction n).sourceTest
          ((1 - rho) - 1 / 2) = 0 := by
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      centered_add_half]
    exact hsourceOneSub
  have horbitSum :
      (∑ u ∈ centeredFunctionalEquationOrbit rho,
        laplaceAt (selectedOwner base correction n).convolutionSquare u) =
          -2 :=
    selectedOwner_centeredOrbit_sum_eq_neg_two_of_nonreal
      base correction n rho hoff hnonreal hsourceRho hsourceComp
      hsourceStar hsourceOneSub
  have hsquareZeros :
      ∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        z.1 ∉ sourceFunctionalEquationOrbit rho →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (z.1 - 1 / 2) = 0 := by
    intro z hz
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n z.1 (hsourceZeros z hz)
  have hcenteredTail := selectedOwner_centered_source_distance_bound_lt
    base correction n rho T epsilon htail
  have hsquareTail := selectedOwner_convolutionSquare_tail_of_source_tail
    base correction n rho T epsilon hepsilon htail
  exact ⟨correction, C, n, hcorrectionSupport, hselectedSupport,
    hcenterRho, hcenterComp, hcenterStar, hcenterOneSub, horbitSum,
    hsquareZeros, hC, hcenteredTail, hsquareTail⟩

/-- The collision-safe negative-orbit owner.  Unlike the four-point
specialization, this theorem needs no nonreal premise: the source and centered
orbits are genuine `Finset`s, and the adaptive target-value function gives
the actual orbit sum `-2` in both the two-point and four-point cases. -/
theorem exists_fixedWindows_nearbyZero_negativeOrbit_selectedOwner
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hoff : rho.re ≠ 1 / 2)
    (routeNodes : Finset ℂ)
    {baseLower baseUpper lower upper : ℝ}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ base : CompactLogTest, ∃ T : ℝ,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      0 ≤ T ∧
      ∀ R : ℝ, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : ℝ, ∃ n : ℕ,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support (selectedOwner base correction n).sourceTest.test ⊆
            Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
              (((n + 1 : ℕ) : ℝ) * baseUpper + upper) ∧
          (∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
            laplaceAt (selectedOwner base correction n).sourceTest
                (w.1 - 1 / 2) = negativeSourceOrbitValue rho w) ∧
          (∑ u ∈ centeredFunctionalEquationOrbit rho,
            laplaceAt (selectedOwner base correction n).convolutionSquare u) =
              -2 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ∉ sourceFunctionalEquationOrbit rho →
              laplaceAt (selectedOwner base correction n).convolutionSquare
                (z.1 - 1 / 2) = 0) ∧
          0 ≤ C ∧
          (∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt (selectedOwner base correction n).sourceTest
                    (z - 1 / 2)‖ < epsilon) ∧
          ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
                  ‖laplaceAt
                    (selectedOwner base correction n).convolutionSquare
                    (z - 1 / 2)‖ < epsilon ^ 2 := by
  obtain ⟨base, T, hbaseSupport, _hbaseTargets, hT, hfamily⟩ :=
    exists_fixedWindows_nearbyZero_unscaled_negativeSourceOrbit_assembly
      rho hrho hoff routeNodes hbaseLower hbaseUpper hlower hupper
      epsilon hepsilon
  refine ⟨base, T, hbaseSupport, hT, ?_⟩
  intro R hR
  obtain ⟨correction, C, n, hcorrectionSupport, hsourceSupport,
      hsourceRho, hsourceComp, hsourceTargets, hsourceZeros, hC, htail⟩ :=
    hfamily R hR
  have hselectedSupport :
      Function.support (selectedOwner base correction n).sourceTest.test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
          (((n + 1 : ℕ) : ℝ) * baseUpper + upper) := by
    simpa only [selectedOwner_sourceTest] using
      halfDensityShift_support_subset
        ((convolutionIterate base n).convolution correction) hsourceSupport
  have hcenterTargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
        laplaceAt (selectedOwner base correction n).sourceTest
            (w.1 - 1 / 2) = negativeSourceOrbitValue rho w := by
    intro w
    rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
      centered_add_half]
    exact hsourceTargets w
  have horbitSum :
      (∑ u ∈ centeredFunctionalEquationOrbit rho,
        laplaceAt (selectedOwner base correction n).convolutionSquare u) =
          -2 :=
    selectedOwner_centeredOrbit_sum_eq_neg_two
      base correction n rho hoff hsourceRho hsourceComp hsourceTargets
  have hsquareZeros :
      ∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        z.1 ∉ sourceFunctionalEquationOrbit rho →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (z.1 - 1 / 2) = 0 := by
    intro z hz
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n z.1 (hsourceZeros z hz)
  have hcenteredTail := selectedOwner_centered_source_distance_bound_lt
    base correction n rho T epsilon htail
  have hsquareTail := selectedOwner_convolutionSquare_tail_of_source_tail
    base correction n rho T epsilon hepsilon htail
  exact ⟨correction, C, n, hcorrectionSupport, hselectedSupport,
    hcenterTargets, horbitSum, hsquareZeros, hC, hcenteredTail, hsquareTail⟩

end UnscaledYoshidaSelectedOwner
end CCM25Concrete
end Source
end ConnesWeilRH
