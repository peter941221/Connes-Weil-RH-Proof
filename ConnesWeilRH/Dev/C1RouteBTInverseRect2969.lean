import ConnesWeilRH.Dev.C1RouteBTSourceNonzero2968

namespace ConnesWeilRH.Dev

noncomputable def routeBTInverseRect2969 : ComplexRect2427 :=
  ComplexRect2427.mk (-25 : ℝ) 25 (-25 : ℝ) 25

theorem routeBTInverseRectMem2969 {t : ℂ}
    (ht : ComplexRect2427.Mem t routeBTSourceRect2968) :
    ComplexRect2427.Mem t⁻¹ routeBTInverseRect2969 := by
  have htlo := ht.2.2.1
  have hthi := ht.2.2.2
  norm_num [routeBTSourceRect2968, ComplexRect2427.mk] at htlo hthi
  have him_nonpos : t.im ≤ 0 := by linarith
  have habsim : (4280 : ℝ) / 100000 ≤ |t.im| := by
    rw [abs_of_nonpos him_nonpos]
    linarith [hthi]
  have hnormLower : (1 : ℝ) / 25 ≤ ‖t‖ := by
    have hcoord : |t.im| ≤ ‖t‖ := RCLike.abs_im_le_norm t
    linarith
  have htnz : t ≠ 0 := routeBTSourceNonzero2968 ht
  have hnormpos : 0 < ‖t‖ := norm_pos_iff.mpr htnz
  have hinvnorm : ‖t⁻¹‖ ≤ (25 : ℝ) := by
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / 25) hnormLower
    norm_num at h ⊢
    exact h
  have hre : |(t⁻¹).re| ≤ (25 : ℝ) := by
    exact le_trans (RCLike.abs_re_le_norm t⁻¹) hinvnorm
  have him : |(t⁻¹).im| ≤ (25 : ℝ) := by
    exact le_trans (RCLike.abs_im_le_norm t⁻¹) hinvnorm
  rw [abs_le] at hre him
  change (-25 : ℝ) ≤ (t⁻¹).re ∧ (t⁻¹).re ≤ 25 ∧
    (-25 : ℝ) ≤ (t⁻¹).im ∧ (t⁻¹).im ≤ 25
  exact ⟨hre.1, hre.2, him.1, him.2⟩

end ConnesWeilRH.Dev
