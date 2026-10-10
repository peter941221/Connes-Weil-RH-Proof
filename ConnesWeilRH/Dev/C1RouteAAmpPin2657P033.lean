import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 033 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 033. -/
def ampArg2657P033 : ℚ := (-233438235938024688027073084545858167425999462210599675 / 4543625902757110809830480684310834372732837284544512)

/-- Stored center of the certified ball for `exp (ampArg2657P033)`. -/
def ampValue2657P033 : ℚ := (812093207422587476511917594802870781365980137601333254091398734638383553 / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192)

/-- Stored radius of the certified ball for `exp (ampArg2657P033)`. -/
def ampRadius2657P033 : ℚ := (67096982334971651843831127 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P033 :
    compactExp2620 (ampArg2657P033 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P033, 0), ampRadius2657P033) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P033 :
    |Real.exp ((ampArg2657P033 : ℝ)) - (ampValue2657P033 : ℝ)|
      ≤ (ampRadius2657P033 : ℝ) := by
  have harg : ampArg2657P033 = (-233438235938024688027073084545858167425999462210599675 / 4543625902757110809830480684310834372732837284544512) := rfl
  have hsmall : |((ampArg2657P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P033 20 hsmall
  rw [ampChain2657P033] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
