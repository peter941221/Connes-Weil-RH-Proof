import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 153 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 153. -/
def ampArg2657P153 : ℚ := (-204922799550763725041841766493335045377818374911717675 / 4806696197476673335107143954199765316270905142280192)

/-- Stored center of the certified ball for `exp (ampArg2657P153)`. -/
def ampValue2657P153 : ℚ := (652258120486659196102829251006424162378617860145557011953036408527391451863069 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P153)`. -/
def ampRadius2657P153 : ℚ := (103358929220982663467475800741 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P153 :
    compactExp2620 (ampArg2657P153 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P153, 0), ampRadius2657P153) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P153 :
    |Real.exp ((ampArg2657P153 : ℝ)) - (ampValue2657P153 : ℝ)|
      ≤ (ampRadius2657P153 : ℝ) := by
  have harg : ampArg2657P153 = (-204922799550763725041841766493335045377818374911717675 / 4806696197476673335107143954199765316270905142280192) := rfl
  have hsmall : |((ampArg2657P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P153 20 hsmall
  rw [ampChain2657P153] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
