import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Record 2276: the stored family cannot use the legacy physical width

The integral a * integral phi_a(x) * exp(a * s * x) dx has physical
coordinate y = a*x and profile phi_a(y/a) = phi_(a^2)(y).
The legacy physical screen instead uses phi_a(y). At y = 6 every legacy
family is zero, whereas exactly stored family 4 survives at squared width.
This is a support no-go, not a strip estimate or an RH claim.
-/

namespace ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

open scoped BigOperators

noncomputable def storedWidth : Fin 30 → ℝ :=
  ![(3602879701896397 / 2251799813685248),
    (517913957147607 / 281474976710656),
    (1170935903116329 / 562949953421312),
    (5224175567749775 / 2251799813685248),
    (1441151880758559 / 562949953421312),
    (3783023686991217 / 2251799813685248),
    2,
    (5224175567749775 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248),
    (3963167672086037 / 2251799813685248)]

noncomputable def widthBump (radius position : ℝ) : ℝ :=
  if |position| < radius then
    Real.exp (-30 / (1 - (position / radius) ^ 2))
  else 0

noncomputable def physicalFamilySum (coefficients : Fin 30 → ℂ)
    (modulations radii : Fin 30 → ℝ) (position : ℝ) : ℂ :=
  ∑ index : Fin 30, coefficients index * (widthBump (radii index) position : ℂ) *
    Complex.exp ((modulations index * position : ℝ) * Complex.I)

noncomputable def legacyPhysical (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) : ℝ → ℂ :=
  physicalFamilySum coefficients modulations storedWidth

noncomputable def correctedPhysical (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) : ℝ → ℂ :=
  physicalFamilySum coefficients modulations (fun index => storedWidth index ^ 2)

noncomputable def storedBaseFour : ℂ :=
  ((-2679001875721701 / 262144) : ℝ) + ((-3001940793386885 / 4194304) : ℝ) * Complex.I

noncomputable def storedCorrFour : ℂ :=
  ((-6001732121601347 / 32) : ℝ) + ((-3369790430725407 / 64) : ℝ) * Complex.I

theorem storedWidth_le_six (index : Fin 30) : storedWidth index ≤ 6 := by
  fin_cases index <;> norm_num [storedWidth]

theorem other_squared_width_le_six (index : Fin 30) (hindex : index ≠ 4) :
    storedWidth index ^ 2 ≤ 6 := by
  fin_cases index <;> norm_num [storedWidth, Fin.ext_iff] at *

theorem fourth_squared_width_gt_six : 6 < storedWidth 4 ^ 2 := by
  change (6 : ℝ) < (1441151880758559 / 562949953421312 : ℝ) ^ 2
  norm_num

theorem legacyPhysical_six_eq_zero (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) : legacyPhysical coefficients modulations 6 = 0 := by
  unfold legacyPhysical physicalFamilySum
  apply Finset.sum_eq_zero
  intro index _
  have houtside : ¬ |(6 : ℝ)| < storedWidth index := by
    simpa using not_lt.mpr (storedWidth_le_six index)
  simp only [widthBump, if_neg houtside, Complex.ofReal_zero, mul_zero, zero_mul]

theorem correctedPhysical_six_eq (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    correctedPhysical coefficients modulations 6 =
      coefficients 4 * (widthBump (storedWidth 4 ^ 2) 6 : ℂ) *
        Complex.exp ((modulations 4 * 6 : ℝ) * Complex.I) := by
  unfold correctedPhysical physicalFamilySum
  apply Finset.sum_eq_single (4 : Fin 30)
  · intro index _ hindex
    have houtside : ¬ |(6 : ℝ)| < storedWidth index ^ 2 := by
      simpa using not_lt.mpr (other_squared_width_le_six index hindex)
    simp only [widthBump, if_neg houtside, Complex.ofReal_zero, mul_zero, zero_mul]
  · simp

theorem fourth_bump_six_pos : 0 < widthBump (storedWidth 4 ^ 2) 6 := by
  have hinside : |(6 : ℝ)| < storedWidth 4 ^ 2 := by
    simpa using fourth_squared_width_gt_six
  rw [widthBump, if_pos hinside]
  exact Real.exp_pos _

theorem correctedPhysical_six_ne_zero (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) (hfour : coefficients 4 ≠ 0) :
    correctedPhysical coefficients modulations 6 ≠ 0 := by
  rw [correctedPhysical_six_eq]
  apply mul_ne_zero
  · apply mul_ne_zero hfour
    exact_mod_cast ne_of_gt fourth_bump_six_pos
  · exact Complex.exp_ne_zero _

theorem physical_owner_ne (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) (hfour : coefficients 4 ≠ 0) :
    correctedPhysical coefficients modulations ≠ legacyPhysical coefficients modulations := by
  intro hequal
  have hvalue := congrFun hequal 6
  rw [legacyPhysical_six_eq_zero] at hvalue
  exact correctedPhysical_six_ne_zero coefficients modulations hfour hvalue

theorem storedBaseFour_ne_zero : storedBaseFour ≠ 0 := by
  intro hzero
  have hreal := congrArg Complex.re hzero
  norm_num [storedBaseFour] at hreal

theorem storedCorrFour_ne_zero : storedCorrFour ≠ 0 := by
  intro hzero
  have hreal := congrArg Complex.re hzero
  norm_num [storedCorrFour] at hreal

theorem stored_base_owner_ne (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) (hfour : coefficients 4 = storedBaseFour) :
    correctedPhysical coefficients modulations ≠ legacyPhysical coefficients modulations := by
  apply physical_owner_ne coefficients modulations
  rw [hfour]
  exact storedBaseFour_ne_zero

theorem stored_corr_owner_ne (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) (hfour : coefficients 4 = storedCorrFour) :
    correctedPhysical coefficients modulations ≠ legacyPhysical coefficients modulations := by
  apply physical_owner_ne coefficients modulations
  rw [hfour]
  exact storedCorrFour_ne_zero

end ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
