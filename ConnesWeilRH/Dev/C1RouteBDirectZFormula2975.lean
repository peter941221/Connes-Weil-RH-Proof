import ConnesWeilRH.Dev.C1RouteBExpDenominatorNonzero2964
import ConnesWeilRH.Dev.C1RouteBTSourceNonzero2968

namespace ConnesWeilRH.Dev

theorem routeBDirectZReFormula2975 {w t : ℂ}
    (hw : w + 1 ≠ 0) (ht : t ≠ 0) :
    (((w - 1) * (w + 1)⁻¹) / t).re =
      (((w.re ^ 2 + w.im ^ 2 - 1) * t.re + 2 * w.im * t.im) /
        (Complex.normSq (w + 1) * Complex.normSq t)) := by
  have hdenw : Complex.normSq (w + 1) ≠ 0 :=
    ne_of_gt ((Complex.normSq_pos).mpr hw)
  have hdent : Complex.normSq t ≠ 0 :=
    ne_of_gt ((Complex.normSq_pos).mpr ht)
  simp only [div_eq_mul_inv]
  rw [Complex.mul_re]
  rw [Complex.inv_re, Complex.inv_im]
  rw [Complex.mul_re, Complex.mul_im]
  rw [Complex.normSq_apply]
  field_simp [hdenw, hdent]
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  have hwpos : 0 < 1 + w.re * 2 + w.re ^ 2 + w.im ^ 2 := by
    have h := Complex.normSq_pos.mpr hw
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im] at h
    nlinarith
  have htpos : 0 < t.re ^ 2 + t.im ^ 2 := by
    have h := Complex.normSq_pos.mpr ht
    simp [Complex.normSq_apply] at h
    nlinarith
  field_simp [ne_of_gt hwpos, ne_of_gt htpos]
  ring_nf
  field_simp [ne_of_gt hwpos, ne_of_gt htpos]
  ring

theorem routeBDirectZImFormula2975 {w t : ℂ}
    (hw : w + 1 ≠ 0) (ht : t ≠ 0) :
    (((w - 1) * (w + 1)⁻¹) / t).im =
      ((2 * w.im * t.re - (w.re ^ 2 + w.im ^ 2 - 1) * t.im) /
        (Complex.normSq (w + 1) * Complex.normSq t)) := by
  have hdenw : Complex.normSq (w + 1) ≠ 0 :=
    ne_of_gt ((Complex.normSq_pos).mpr hw)
  have hdent : Complex.normSq t ≠ 0 :=
    ne_of_gt ((Complex.normSq_pos).mpr ht)
  simp only [div_eq_mul_inv]
  rw [Complex.mul_im]
  rw [Complex.inv_re, Complex.inv_im]
  rw [Complex.mul_re, Complex.mul_im]
  rw [Complex.normSq_apply]
  field_simp [hdenw, hdent]
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  have hwpos : 0 < 1 + w.re * 2 + w.re ^ 2 + w.im ^ 2 := by
    have h := Complex.normSq_pos.mpr hw
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im] at h
    nlinarith
  have htpos : 0 < t.re ^ 2 + t.im ^ 2 := by
    have h := Complex.normSq_pos.mpr ht
    simp [Complex.normSq_apply] at h
    nlinarith
  field_simp [ne_of_gt hwpos, ne_of_gt htpos]
  ring_nf
  field_simp [ne_of_gt hwpos, ne_of_gt htpos]
  ring

end ConnesWeilRH.Dev
