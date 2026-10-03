import ConnesWeilRH.Dev.C1RouteABaseCoefficientBoxes2540
import ConnesWeilRH.Dev.C1RouteASignedAggregateCell2539
import ConnesWeilRH.Dev.C1RouteAExpSplit2498

/-! The exact center node of the 10240-cell production grid, with the
record-2338 coefficient rectangles. The numerical upper is proved here;
membership of the actual interpolation coefficients remains a premise. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

private theorem sum30_chain2540 (f : Fin 30 → ℝ) :
    (∑ i, f i) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 +
      (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 +
      (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + f 29
      )))))))))))))))))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem baseBox_re_lower2540 :
    (147426599914317 : ℝ) ≤ ∑ i : Fin 30, (baseCoefficientBox2540 i).reLo := by
  rw [sum30_chain2540]
  norm_num [baseCoefficientBox2540]

theorem baseBox_re_upper2540 :
    (∑ i : Fin 30, (baseCoefficientBox2540 i).reHi) ≤ (147426599914319 : ℝ) := by
  rw [sum30_chain2540]
  norm_num [baseCoefficientBox2540]

theorem baseBox_im_lower2540 :
    (18836521581 : ℝ) ≤ ∑ i : Fin 30, (baseCoefficientBox2540 i).imLo := by
  rw [sum30_chain2540]
  norm_num [baseCoefficientBox2540]

theorem baseBox_im_upper2540 :
    (∑ i : Fin 30, (baseCoefficientBox2540 i).imHi) ≤ (18836521582 : ℝ) := by
  rw [sum30_chain2540]
  norm_num [baseCoefficientBox2540]

theorem baseCoefficient_sum_norm_le2540 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖∑ i, coefficients i‖ ≤ (147445436435901 : ℝ) := by
  have hs := ComplexRect2427.mem_sumFinset (s := Finset.univ)
    (fun i _ => hbox i)
  change (∑ i, (baseCoefficientBox2540 i).reLo) ≤ (∑ i, coefficients i).re ∧
    (∑ i, coefficients i).re ≤ (∑ i, (baseCoefficientBox2540 i).reHi) ∧
    (∑ i, (baseCoefficientBox2540 i).imLo) ≤ (∑ i, coefficients i).im ∧
    (∑ i, coefficients i).im ≤ (∑ i, (baseCoefficientBox2540 i).imHi) at hs
  have hre0 : 0 ≤ (∑ i, coefficients i).re := by
    linarith [baseBox_re_lower2540, hs.1]
  have him0 : 0 ≤ (∑ i, coefficients i).im := by
    linarith [baseBox_im_lower2540, hs.2.2.1]
  have hn := Complex.norm_le_abs_re_add_abs_im (∑ i, coefficients i)
  rw [abs_of_nonneg hre0, abs_of_nonneg him0] at hn
  linarith [baseBox_re_upper2540, baseBox_im_upper2540, hs.2.1, hs.2.2.2]

theorem exp_neg_thirty_upper2540 :
    Real.exp (-30 : ℝ) ≤ (9358 : ℝ) / 100000000000000000 := by
  have hp := pow_le_pow_left₀ (Real.exp_pos (-1)).le
    exp_neg_one_le_expNegOneUpper2498 30
  have heq : Real.exp (-30 : ℝ) = Real.exp (-1 : ℝ) ^ 30 := by
    simpa using Real.exp_nat_mul (-1 : ℝ) 30
  rw [heq]
  apply hp.trans
  norm_num [expNegOneUpper2498]

theorem weightedPhysical_center_eq2540 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    weightedPhysical2539 sigma coefficients modulations 0 =
      (∑ i, coefficients i) * (Real.exp (-30 : ℝ) : ℂ) := by
  simp only [weightedPhysical2539, weightedFunction2348, weightedExp2348, mul_zero,
    Real.exp_zero, Complex.ofReal_one, one_mul, externalPhysical2344]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hr : (0 : ℝ) < storedWidth i ^ 2 := pow_pos (storedWidth_pos i) 2
  simp [externalFamilyValue2344, hr, Complex.ofReal_exp]

theorem weightedPhysical_center_le2540 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 sigma coefficients modulations 0‖ ≤ (6899 : ℝ)/500 := by
  rw [weightedPhysical_center_eq2540, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (147445436435901 : ℝ) * ((9358 : ℝ)/100000000000000000) :=
      mul_le_mul (baseCoefficient_sum_norm_le2540 coefficients hbox)
        exp_neg_thirty_upper2540 (Real.exp_pos _).le (by norm_num)
    _ ≤ _ := by norm_num

theorem production_grid_center2540 :
    -stripRadius2303 + (5120 : ℝ)*(2*stripRadius2303/10240) = 0 := by ring

noncomputable def baseCoefficientCenter2540 (i : Fin 30) : ℂ :=
  ⟨((baseCoefficientBox2540 i).reLo + (baseCoefficientBox2540 i).reHi)/2,
    ((baseCoefficientBox2540 i).imLo + (baseCoefficientBox2540 i).imHi)/2⟩

noncomputable def baseCoefficientError2540 (_ : Fin 30) : ℝ := 1/10^30

theorem baseBox_widths2540 (i : Fin 30) :
    (baseCoefficientBox2540 i).reLo ≤ (baseCoefficientBox2540 i).reHi ∧
    (baseCoefficientBox2540 i).imLo ≤ (baseCoefficientBox2540 i).imHi ∧
    ((baseCoefficientBox2540 i).reHi - (baseCoefficientBox2540 i).reLo)/2 +
      ((baseCoefficientBox2540 i).imHi - (baseCoefficientBox2540 i).imLo)/2 ≤
      baseCoefficientError2540 i := by
  fin_cases i <;> norm_num [baseCoefficientBox2540, baseCoefficientError2540]

theorem baseCoefficientCenter_mem2540 (i : Fin 30) :
    (baseCoefficientBox2540 i).Mem (baseCoefficientCenter2540 i) := by
  have h := baseBox_widths2540 i
  change _ ≤ (_+_)/2 ∧ (_+_)/2 ≤ _ ∧ _ ≤ (_+_)/2 ∧ (_+_)/2 ≤ _
  constructor
  · linarith [h.1]
  constructor
  · linarith [h.1]
  constructor <;> linarith [h.2.1]

theorem baseCoefficient_error_of_box2540 (i : Fin 30) (c : ℂ)
    (hbox : (baseCoefficientBox2540 i).Mem c) :
    ‖c - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i := by
  have hr : |(c - baseCoefficientCenter2540 i).re| ≤
      ((baseCoefficientBox2540 i).reHi - (baseCoefficientBox2540 i).reLo)/2 := by
    change |c.re - (_+_)/2| ≤ _
    apply abs_le.mpr
    constructor <;> linarith [hbox.1, hbox.2.1]
  have hi : |(c - baseCoefficientCenter2540 i).im| ≤
      ((baseCoefficientBox2540 i).imHi - (baseCoefficientBox2540 i).imLo)/2 := by
    change |c.im - (_+_)/2| ≤ _
    apply abs_le.mpr
    constructor <;> linarith [hbox.2.2.1, hbox.2.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans
    ((add_le_add hr hi).trans (baseBox_widths2540 i).2.2)

theorem signedJet_center_le2540 (sigma : ℝ) (modulations : Fin 30 → ℝ) :
    signedJetUpper2539 0 sigma baseCoefficientCenter2540 baseCoefficientError2540
      modulations 0 ≤ (69 : ℝ)/5 := by
  have hc := weightedPhysical_center_le2540 sigma baseCoefficientCenter2540 modulations
    baseCoefficientCenter_mem2540
  have heach : ∀ i : Fin 30,
      baseCoefficientError2540 i * ‖weightedUnitJet2539 0 sigma modulations i 0‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have hr : (0 : ℝ) < storedWidth i ^ 2 := pow_pos (storedWidth_pos i) 2
    have hu : weightedUnitJet2539 0 sigma modulations i 0 =
        (Real.exp (-30 : ℝ) : ℂ) := by
      simp [weightedUnitJet2539, weightedFunction2348, weightedExp2348, externalFamilyValue2344,
        hr, Complex.ofReal_exp]
    rw [hu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change (1 : ℝ)/10^30 * Real.exp (-30) ≤ _
    have he : Real.exp (-30 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have hsum : (∑ i : Fin 30,
      baseCoefficientError2540 i * ‖weightedUnitJet2539 0 sigma modulations i 0‖) ≤
        (30 : ℝ)/10^30 := by simpa using hs
  have hid := weightedPhysical2539_iteratedDeriv 0 sigma baseCoefficientCenter2540
    modulations 0
  simp only [iteratedDeriv_zero] at hid
  unfold signedJetUpper2539
  rw [← hid]
  linarith

end ConnesWeilRH.Dev
