/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Selected CCM25 Weil formula

The pole, archimedean, and prime-power terms below all read the same selected
convolution square. The archimedean integral carries an explicit integrability
witness before it can enter the formula owner.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete

open MeasureTheory
open scoped ComplexConjugate ContDiff

namespace SelectedWeilFormula

open SelectedWeilSquare

end SelectedWeilFormula

namespace SelectedWeilSquare
namespace SelectedWeilSquareOwner

/-- Bilateral Laplace evaluation of the compact convolution square. -/
noncomputable def laplaceAt
    (owner : SelectedWeilSquareOwner) (s : ℝ) : ℂ :=
  ∫ x : ℝ,
    Complex.exp ((s : ℂ) * x) * owner.convolutionSquare.test x

theorem laplaceIntegrand_integrable
    (owner : SelectedWeilSquareOwner) (s : ℝ) :
    Integrable
      (fun x : ℝ =>
        Complex.exp ((s : ℂ) * x) * owner.convolutionSquare.test x) := by
  have hcontinuous : Continuous
      (fun x : ℝ =>
        Complex.exp ((s : ℂ) * x) * owner.convolutionSquare.test x) := by
    fun_prop
  have hcompact : HasCompactSupport
      (fun x : ℝ =>
        Complex.exp ((s : ℂ) * x) * owner.convolutionSquare.test x) :=
    owner.convolutionSquare.compactSupport.mul_left
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

theorem laplaceAt_neg
    (owner : SelectedWeilSquareOwner) (s : ℝ) :
    owner.laplaceAt (-s) = star (owner.laplaceAt s) := by
  rw [laplaceAt, laplaceAt]
  simp only [Complex.star_def]
  rw [← integral_conj]
  let reflected : ℝ → ℂ := fun x =>
    Complex.exp (((-s : ℝ) : ℂ) * x) * owner.convolutionSquare.test x
  calc
    (∫ x : ℝ, Complex.exp (((-s : ℝ) : ℂ) * x) *
        owner.convolutionSquare.test x) =
        ∫ x : ℝ, reflected (-x) := by
      exact (integral_neg_eq_self reflected (volume : Measure ℝ)).symm
    _ = ∫ x : ℝ, conj
        (Complex.exp ((s : ℂ) * x) * owner.convolutionSquare.test x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [reflected, Complex.ofReal_neg]
      rw [owner.convolutionSquare_neg]
      have hexp :
          Complex.exp ((-(s : ℂ)) * (-(x : ℂ))) =
            conj (Complex.exp ((s : ℂ) * x)) := by
        rw [← Complex.exp_conj]
        congr 1
        simp
      rw [hexp]
      simp only [map_mul, Complex.star_def]

/-- The two pole evaluations in CCM25 Eq. (3.11). -/
noncomputable def poleTerm
    (owner : SelectedWeilSquareOwner) : ℂ :=
  owner.laplaceAt (1 / 2) + owner.laplaceAt (-1 / 2)

theorem poleTerm_im_eq_zero
    (owner : SelectedWeilSquareOwner) :
    owner.poleTerm.im = 0 := by
  rw [poleTerm, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    owner.laplaceAt_neg]
  simp

/-- The numerator of the archimedean density after `x = exp y`. -/
noncomputable def archimedeanNumerator
    (owner : SelectedWeilSquareOwner) (y : ℝ) : ℂ :=
  (Complex.ofRealCLM (Real.exp (y / 2)) *
      (owner.convolutionSquare.test y + owner.convolutionSquare.test (-y)) -
        2 * owner.convolutionSquare.test 0)

/-- The denominator `2 sinh y` of the archimedean density. -/
noncomputable def archimedeanDenominator (y : ℝ) : ℝ :=
  Real.exp y - Real.exp (-y)

/-- The archimedean density in the formula following CCM25 Eq. (3.7). -/
noncomputable def archimedeanIntegrand
    (owner : SelectedWeilSquareOwner) (y : ℝ) : ℂ :=
  owner.archimedeanNumerator y / (archimedeanDenominator y : ℂ)

@[simp] theorem archimedeanNumerator_zero
    (owner : SelectedWeilSquareOwner) :
    owner.archimedeanNumerator 0 = 0 := by
  simp [archimedeanNumerator]
  ring

@[simp] theorem archimedeanDenominator_zero :
    archimedeanDenominator 0 = 0 := by
  simp [archimedeanDenominator]

theorem archimedeanNumerator_contDiff
    (owner : SelectedWeilSquareOwner) :
    ContDiff ℝ ∞ owner.archimedeanNumerator := by
  unfold archimedeanNumerator
  fun_prop

theorem archimedeanDenominator_contDiff :
    ContDiff ℝ ∞ archimedeanDenominator := by
  unfold archimedeanDenominator
  fun_prop

theorem archimedeanNumerator_im_eq_zero
    (owner : SelectedWeilSquareOwner) (y : ℝ) :
    (owner.archimedeanNumerator y).im = 0 := by
  have hexp_im : (Complex.exp ((y : ℂ) / 2)).im = 0 := by
    rw [show (y : ℂ) / 2 = ((y / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.exp_ofReal_im (y / 2)
  rw [archimedeanNumerator, owner.convolutionSquare_add_neg_eq_two_re,
    Complex.sub_im, Complex.mul_im, Complex.mul_im,
    owner.convolutionSquare_zero_im]
  simp [hexp_im]

theorem archimedeanIntegrand_im_eq_zero
    (owner : SelectedWeilSquareOwner) (y : ℝ) :
    (owner.archimedeanIntegrand y).im = 0 := by
  rw [archimedeanIntegrand, Complex.div_im]
  simp [owner.archimedeanNumerator_im_eq_zero]

/-- The explicit archimedean distribution, conditional only on integrability. -/
noncomputable def archimedeanTerm
    (owner : SelectedWeilSquareOwner) : ℂ :=
  (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) *
      owner.convolutionSquare.test 0) +
    ∫ y in Set.Ioi (0 : ℝ), owner.archimedeanIntegrand y

end SelectedWeilSquareOwner
end SelectedWeilSquare

namespace SelectedWeilFormula

open SelectedWeilSquare

/-- The one remaining analytic legality witness for the explicit formula. -/
structure SelectedArchimedeanData
    (owner : SelectedWeilSquareOwner) where
  integrable : IntegrableOn owner.archimedeanIntegrand (Set.Ioi (0 : ℝ))

/-- All components of the selected Weil formula share one square owner. -/
structure SelectedWeilFormulaOwner where
  square : SelectedWeilSquareOwner
  finiteSupport : SelectedFinitePrimeSupportData square :=
    SelectedFinitePrimeSupportData.ofOwner square
  archimedean : SelectedArchimedeanData square

namespace SelectedWeilFormulaOwner

theorem archimedeanIntegral_im_eq_zero
    (owner : SelectedWeilFormulaOwner) :
    (∫ y in Set.Ioi (0 : ℝ), owner.square.archimedeanIntegrand y).im = 0 := by
  calc
    (∫ y in Set.Ioi (0 : ℝ), owner.square.archimedeanIntegrand y).im =
        ∫ y in Set.Ioi (0 : ℝ), (owner.square.archimedeanIntegrand y).im := by
      symm
      simpa only [RCLike.im_eq_complex_im] using
        integral_im owner.archimedean.integrable
    _ = 0 := by
      simp only [owner.square.archimedeanIntegrand_im_eq_zero, integral_zero]

theorem archimedeanTerm_im_eq_zero
    (owner : SelectedWeilFormulaOwner) :
    owner.square.archimedeanTerm.im = 0 := by
  rw [SelectedWeilSquareOwner.archimedeanTerm, Complex.add_im,
    Complex.mul_im, owner.square.convolutionSquare_zero_im,
    owner.archimedeanIntegral_im_eq_zero]
  simp

noncomputable def globalFinitePrimeTerm
    (owner : SelectedWeilFormulaOwner) : ℂ :=
  ∑ n ∈ owner.finiteSupport.globalPrimeIndexSet,
    owner.square.finitePrimeTerm n

noncomputable def restrictedFinitePrimeTerm
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) : ℂ :=
  ∑ n ∈ owner.finiteSupport.restrictedPrimeIndexSet lambda,
    owner.square.finitePrimeTerm n

/-- Prime-power terms present globally but omitted by the `lambda` cutoff. -/
noncomputable def omittedFinitePrimeTerm
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) : ℂ :=
  ∑ n ∈ owner.finiteSupport.globalPrimeIndexSet \
      owner.finiteSupport.restrictedPrimeIndexSet lambda,
    owner.square.finitePrimeTerm n

theorem globalFinitePrimeTerm_im_eq_zero
    (owner : SelectedWeilFormulaOwner) :
    owner.globalFinitePrimeTerm.im = 0 := by
  rw [globalFinitePrimeTerm, Complex.im_sum]
  simp only [owner.square.finitePrimeTerm_im_eq_zero, Finset.sum_const_zero]

theorem restrictedFinitePrimeTerm_im_eq_zero
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    (owner.restrictedFinitePrimeTerm lambda).im = 0 := by
  rw [restrictedFinitePrimeTerm, Complex.im_sum]
  simp only [owner.square.finitePrimeTerm_im_eq_zero, Finset.sum_const_zero]

theorem omittedFinitePrimeTerm_im_eq_zero
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    (owner.omittedFinitePrimeTerm lambda).im = 0 := by
  rw [omittedFinitePrimeTerm, Complex.im_sum]
  simp only [owner.square.finitePrimeTerm_im_eq_zero, Finset.sum_const_zero]

/-- `Psi(F_g) = W_0,2(F_g) - W_R(F_g) - sum_p W_p(F_g)`. -/
noncomputable def weilValue
    (owner : SelectedWeilFormulaOwner) : ℂ :=
  owner.square.poleTerm - owner.square.archimedeanTerm -
    owner.globalFinitePrimeTerm

noncomputable def restrictedWeilValue
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) : ℂ :=
  owner.square.poleTerm - owner.square.archimedeanTerm -
    owner.restrictedFinitePrimeTerm lambda

theorem weilValue_im_eq_zero
    (owner : SelectedWeilFormulaOwner) :
    owner.weilValue.im = 0 := by
  simp [weilValue, owner.square.poleTerm_im_eq_zero,
    owner.archimedeanTerm_im_eq_zero,
    owner.globalFinitePrimeTerm_im_eq_zero]

theorem restrictedWeilValue_im_eq_zero
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    (owner.restrictedWeilValue lambda).im = 0 := by
  simp [restrictedWeilValue, owner.square.poleTerm_im_eq_zero,
    owner.archimedeanTerm_im_eq_zero,
    owner.restrictedFinitePrimeTerm_im_eq_zero]

@[simp] theorem globalFinitePrimeTerm_eq
    (owner : SelectedWeilFormulaOwner) :
    owner.globalFinitePrimeTerm =
      ∑ n ∈ owner.finiteSupport.globalPrimeIndexSet,
        owner.square.finitePrimeTerm n :=
  rfl

@[simp] theorem restrictedFinitePrimeTerm_eq
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    owner.restrictedFinitePrimeTerm lambda =
      ∑ n ∈ owner.finiteSupport.restrictedPrimeIndexSet lambda,
        owner.square.finitePrimeTerm n :=
  rfl

theorem restrictedPrimeIndexSet_subset_global
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    owner.finiteSupport.restrictedPrimeIndexSet lambda ⊆
      owner.finiteSupport.globalPrimeIndexSet := by
  intro n hn
  have hrestricted :=
    (owner.finiteSupport.restrictedExact lambda n).1 hn
  exact (owner.finiteSupport.globalExact n).2
    ⟨hrestricted.1, hrestricted.2.1⟩

theorem mem_omittedPrimeIndexSet_iff
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) (n : ℕ) :
    n ∈ owner.finiteSupport.globalPrimeIndexSet \
        owner.finiteSupport.restrictedPrimeIndexSet lambda ↔
      IsPrimePow n ∧ owner.square.finitePrimeTerm n ≠ 0 ∧
        ¬(1 < n ∧ (n : ℝ) ≤ lambda ^ 2) := by
  rw [Finset.mem_sdiff, owner.finiteSupport.globalExact,
    owner.finiteSupport.restrictedExact]
  tauto

theorem globalFinitePrimeTerm_eq_restricted_add_omitted
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    owner.globalFinitePrimeTerm =
      owner.restrictedFinitePrimeTerm lambda +
        owner.omittedFinitePrimeTerm lambda := by
  rw [globalFinitePrimeTerm, restrictedFinitePrimeTerm,
    omittedFinitePrimeTerm]
  have hsubset := owner.restrictedPrimeIndexSet_subset_global lambda
  simpa [add_comm] using
    (Finset.sum_sdiff (f := fun n => owner.square.finitePrimeTerm n) hsubset).symm

/-- The full/restricted discrepancy is exactly the omitted prime-power sum. -/
theorem restrictedWeilValue_eq_weilValue_add_omitted
    (owner : SelectedWeilFormulaOwner) (lambda : ℝ) :
    owner.restrictedWeilValue lambda =
      owner.weilValue + owner.omittedFinitePrimeTerm lambda := by
  rw [restrictedWeilValue, weilValue,
    owner.globalFinitePrimeTerm_eq_restricted_add_omitted lambda]
  ring

end SelectedWeilFormulaOwner
end SelectedWeilFormula
end CCM25Concrete
end Source
end ConnesWeilRH
