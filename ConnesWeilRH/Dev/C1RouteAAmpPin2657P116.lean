import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 116 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 116. -/
def ampArg2657P116 : ℚ := (-70534458846973348237805654375490881754716081236324775 / 2323239540242136551349532502206621395120561768628224)

/-- Stored center of the certified ball for `exp (ampArg2657P116)`. -/
def ampValue2657P116 : ℚ := (2178054432540941376401891753827940589551306909322291186176136889867504486256439065 / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384)

/-- Stored radius of the certified ball for `exp (ampArg2657P116)`. -/
def ampRadius2657P116 : ℚ := (88354942466180329621130213446410959 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P116 :
    compactExp2620 (ampArg2657P116 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P116, 0), ampRadius2657P116) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P116 :
    |Real.exp ((ampArg2657P116 : ℝ)) - (ampValue2657P116 : ℝ)|
      ≤ (ampRadius2657P116 : ℝ) := by
  have harg : ampArg2657P116 = (-70534458846973348237805654375490881754716081236324775 / 2323239540242136551349532502206621395120561768628224) := rfl
  have hsmall : |((ampArg2657P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P116 20 hsmall
  rw [ampChain2657P116] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
