import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerGrid3212

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff

/-
3306 keeps the signed real part of the center jet and charges only coefficient
errors by scalar norm terms.  This is the row-provider shape needed by the
3305 signed block consumer; it does not supply the numerical rows or the
sixth-order block inequalities.
-/

noncomputable def signedRealJetUpper3306 (order : ℕ) (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (position : ℝ) : ℝ :=
  (∑ index : Fin 30,
      centers index * weightedUnitJet2539 order sigma modulations index position).re +
    ∑ index : Fin 30,
      errors index * ‖weightedUnitJet2539 order sigma modulations index position‖

theorem weightedExternal3306_real_jet_le
    (order : ℕ) (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    (position : ℝ) :
    iteratedDeriv order
        (weightedExternal3201 sigma coefficients modulations) position ≤
      signedRealJetUpper3306 order sigma centers errors modulations position := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 sigma coefficients modulations) order position
    (weightedPhysical2539_contDiff sigma coefficients modulations)]
  rw [weightedPhysical2539_iteratedDeriv]
  let centerSum : ℂ := ∑ index : Fin 30,
    centers index * weightedUnitJet2539 order sigma modulations index position
  let errorSum : ℂ := ∑ index : Fin 30,
    (coefficients index - centers index) *
      weightedUnitJet2539 order sigma modulations index position
  have hdecomp :
      (∑ index : Fin 30,
        coefficients index * weightedUnitJet2539 order sigma modulations index position) =
        centerSum + errorSum := by
    simp only [centerSum, errorSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index hmem
    ring
  have herror_re : errorSum.re ≤ ‖errorSum‖ := by
    exact (le_abs_self errorSum.re).trans (by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm errorSum)
  have herror_norm :
      ‖errorSum‖ ≤ ∑ index : Fin 30,
        ‖coefficients index - centers index‖ *
          ‖weightedUnitJet2539 order sigma modulations index position‖ := by
    unfold errorSum
    calc
      ‖∑ index : Fin 30,
          (coefficients index - centers index) *
            weightedUnitJet2539 order sigma modulations index position‖ ≤
          ∑ index : Fin 30,
            ‖(coefficients index - centers index) *
              weightedUnitJet2539 order sigma modulations index position‖ := by
        simpa using (norm_sum_le (Finset.univ : Finset (Fin 30))
          (fun index => (coefficients index - centers index) *
            weightedUnitJet2539 order sigma modulations index position))
      _ = ∑ index : Fin 30,
          ‖coefficients index - centers index‖ *
            ‖weightedUnitJet2539 order sigma modulations index position‖ := by
        apply Finset.sum_congr rfl
        intro index hmem
        rw [norm_mul]
  have herror_sum :
      (∑ index : Fin 30,
        ‖coefficients index - centers index‖ *
          ‖weightedUnitJet2539 order sigma modulations index position‖) ≤
        ∑ index : Fin 30,
          errors index *
            ‖weightedUnitJet2539 order sigma modulations index position‖ := by
    apply Finset.sum_le_sum
    intro index hmem
    exact mul_le_mul_of_nonneg_right (herror index) (norm_nonneg _)
  calc
    (∑ index : Fin 30,
        coefficients index * weightedUnitJet2539 order sigma modulations index position).re =
        centerSum.re + errorSum.re := by
          rw [hdecomp]
          change centerSum.re + errorSum.re = centerSum.re + errorSum.re
          rfl
    _ ≤ centerSum.re + ‖errorSum‖ := by
          simpa [add_comm] using add_le_add_left herror_re centerSum.re
    _ ≤ centerSum.re +
        ∑ index : Fin 30,
          ‖coefficients index - centers index‖ *
            ‖weightedUnitJet2539 order sigma modulations index position‖ := by
          simpa [add_comm] using
            add_le_add_left herror_norm centerSum.re
    _ ≤ centerSum.re +
        ∑ index : Fin 30,
          errors index *
            ‖weightedUnitJet2539 order sigma modulations index position‖ := by
          simpa [add_comm] using
            add_le_add_left herror_sum centerSum.re
    _ = signedRealJetUpper3306 order sigma centers errors modulations position := by
          rfl

noncomputable def record2680SignedRealSecondUpper3306 (index : ℕ) : ℝ :=
  signedRealJetUpper3306 2 (-1 / 2) record2680CorrectionCoefficient
    (fun _ => 0) capturedModulations2584 (record2680Center3212 index)

noncomputable def record2680SignedRealFourthUpper3306 (index : ℕ) : ℝ :=
  signedRealJetUpper3306 4 (-1 / 2) record2680CorrectionCoefficient
    (fun _ => 0) capturedModulations2584 (record2680Center3212 index)

theorem record2680_signed_real_second_bound3306
    {index : ℕ} (_hindex : index < 40960) :
    iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      record2680SignedRealSecondUpper3306 index := by
  apply weightedExternal3306_real_jet_le
  intro family
  simp

theorem record2680_signed_real_fourth_bound3306
    {index : ℕ} (_hindex : index < 40960) :
    iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      record2680SignedRealFourthUpper3306 index := by
  apply weightedExternal3306_real_jet_le
  intro family
  simp

end ConnesWeilRH.Dev
