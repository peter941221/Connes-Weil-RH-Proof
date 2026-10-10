import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 031 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 031. -/
def ampArg2657P031 : ℚ := (-77770131425869809010937097987154539809463891414810525 / 1453646066030249315018340026740432998425281905557504)

/-- Stored center of the certified ball for `exp (ampArg2657P031)`. -/
def ampValue2657P031 : ℚ := (6220049627934460256679494372594697856733898637750791258653600283496950957 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P031)`. -/
def ampRadius2657P031 : ℚ := (4547088885992456638477347 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P031 :
    compactExp2620 (ampArg2657P031 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P031, 0), ampRadius2657P031) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P031 :
    |Real.exp ((ampArg2657P031 : ℝ)) - (ampValue2657P031 : ℝ)|
      ≤ (ampRadius2657P031 : ℝ) := by
  have harg : ampArg2657P031 = (-77770131425869809010937097987154539809463891414810525 / 1453646066030249315018340026740432998425281905557504) := rfl
  have hsmall : |((ampArg2657P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P031 20 hsmall
  rw [ampChain2657P031] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
