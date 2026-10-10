import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

/-!
# Complex phase scalar engine (record 2624 GO-route brick 1)

`exp(i * phase)` at an exact rational phase, replayed through the
certified 2620 compact engine: the argument is reduced by `2 ^ index`,
replayed with 320-bit coordinate rounding and a 400-bit rational
radius, and squared back up. The interface theorems give the unit-circle
point as a complex ball and its cosine/sine coordinates with the SAME
stored radius, which is what the complex panel tables multiply into
their Horner chains. `decide`-friendly: every operation is
`RatPair2542` arithmetic on literals.
-/

/-- The phase-exponential ball for `exp(i * phase)`: reduced argument
`(0, phase / 2 ^ index)` replayed by the certified compact engine. -/
def phaseExp2646 (phase : ℚ) (index : ℕ) : RatState2542 :=
  compactExp2620 (0, phase / (2 : ℚ) ^ index) index

theorem embedPhase2646 (phase : ℚ) (index : ℕ) :
    embedPair2542 (0, phase / (2 : ℚ) ^ index) =
      Complex.I * ((phase / (2 : ℚ) ^ index : ℚ) : ℂ) := by
  apply Complex.ext
  · -- `(i * w).re = -w.im`, and `w.im = 0` for a rational point
    simp only [embedPair2542, Complex.mul_re, Complex.I_re, Complex.I_im,
      Rat.cast_zero, zero_mul, one_mul, zero_sub, Complex.ratCast_im, neg_zero]
  · -- `(i * w).im = w.re`, and `w.re` unfolds to the rational cast
    simp only [embedPair2542, Complex.mul_im, Complex.I_re, Complex.I_im,
      one_mul, zero_mul, zero_add, Complex.ratCast_re]

theorem phaseExp_small2646 (phase : ℚ) (index : ℕ)
    (hsmall : |((phase / (2 : ℚ) ^ index : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000) :
    ‖embedPair2542 (0, phase / (2 : ℚ) ^ index)‖ ≤ (1 : ℝ) / 1000 := by
  apply complex_norm_le_l1_2541
  simpa [embedPair2542] using hsmall

theorem phaseExp_exp_error2646 (phase : ℚ) (index : ℕ)
    (hsmall : |((phase / (2 : ℚ) ^ index : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000) :
    ‖Complex.exp (Complex.I * (phase : ℂ)) -
      embedPair2542 (phaseExp2646 phase index).1‖ ≤
      ((phaseExp2646 phase index).2 : ℝ) := by
  have hz := phaseExp_small2646 phase index hsmall
  have h := compactExp_error2620 (0, phase / (2 : ℚ) ^ index) hz index
  rw [embedPhase2646] at h
  have hq : (2 : ℂ) ^ index * ((phase / (2 : ℚ) ^ index : ℚ) : ℂ) =
      (phase : ℂ) := by
    push_cast
    field_simp
  have hexponent : (2 : ℂ) ^ index *
      (Complex.I * ((phase / (2 : ℚ) ^ index : ℚ) : ℂ)) =
      Complex.I * (phase : ℂ) := by
    calc (2 : ℂ) ^ index * (Complex.I * ((phase / (2 : ℚ) ^ index : ℚ) : ℂ))
        = Complex.I *
            ((2 : ℂ) ^ index * ((phase / (2 : ℚ) ^ index : ℚ) : ℂ)) := by ring
      _ = Complex.I * (phase : ℂ) := by rw [hq]
  rw [hexponent] at h
  exact h

/-- Euler extraction, real part: `re (exp (i * t)) = cos t` for real `t`. -/
theorem exp_I_re_cos2646 (t : ℝ) :
    (Complex.exp (Complex.I * ((t : ℝ) : ℂ))).re = Real.cos t := by
  have he : Complex.exp (Complex.I * ((t : ℝ) : ℂ)) =
      Complex.cos ((t : ℝ) : ℂ) + Complex.sin ((t : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_mul_I ((t : ℝ) : ℂ)
  conv_lhs => rw [he]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Euler extraction, imaginary part: `im (exp (i * t)) = sin t`. -/
theorem exp_I_im_sin2646 (t : ℝ) :
    (Complex.exp (Complex.I * ((t : ℝ) : ℂ))).im = Real.sin t := by
  have he : Complex.exp (Complex.I * ((t : ℝ) : ℂ)) =
      Complex.cos ((t : ℝ) : ℂ) + Complex.sin ((t : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_mul_I ((t : ℝ) : ℂ)
  conv_lhs => rw [he]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem phaseExp_cos_error2646 (phase : ℚ) (index : ℕ)
    (hsmall : |((phase / (2 : ℚ) ^ index : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000) :
    |Real.cos (phase : ℝ) - ((phaseExp2646 phase index).1.1 : ℝ)| ≤
      ((phaseExp2646 phase index).2 : ℝ) := by
  have h := phaseExp_exp_error2646 phase index hsmall
  have hcast : ((phase : ℚ) : ℂ) = (((phase : ℚ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hcast] at h
  have hcos : (Complex.exp (Complex.I * (((phase : ℚ) : ℝ) : ℂ))).re =
      Real.cos (phase : ℝ) := exp_I_re_cos2646 _
  have hreal := (Complex.abs_re_le_norm
    (Complex.exp (Complex.I * (((phase : ℚ) : ℝ) : ℂ)) -
      embedPair2542 (phaseExp2646 phase index).1)).trans h
  rw [Complex.sub_re] at hreal
  rw [hcos] at hreal
  simpa [embedPair2542] using hreal

theorem phaseExp_sin_error2646 (phase : ℚ) (index : ℕ)
    (hsmall : |((phase / (2 : ℚ) ^ index : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000) :
    |Real.sin (phase : ℝ) - ((phaseExp2646 phase index).1.2 : ℝ)| ≤
      ((phaseExp2646 phase index).2 : ℝ) := by
  have h := phaseExp_exp_error2646 phase index hsmall
  have hcast : ((phase : ℚ) : ℂ) = (((phase : ℚ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hcast] at h
  have hsin : (Complex.exp (Complex.I * (((phase : ℚ) : ℝ) : ℂ))).im =
      Real.sin (phase : ℝ) := exp_I_im_sin2646 _
  have himag := (Complex.abs_im_le_norm
    (Complex.exp (Complex.I * (((phase : ℚ) : ℝ) : ℂ)) -
      embedPair2542 (phaseExp2646 phase index).1)).trans h
  rw [Complex.sub_im] at himag
  rw [hsin] at himag
  simpa [embedPair2542] using himag

end ConnesWeilRH.Dev
