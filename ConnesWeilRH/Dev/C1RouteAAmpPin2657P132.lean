import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 132 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 132. -/
def ampArg2657P132 : ℚ := (-66319058899973530498766796664177845372819510133473 / 2009564751329991512530066644984889152026907246592)

/-- Stored center of the certified ball for `exp (ampArg2657P132)`. -/
def ampValue2657P132 : ℚ := (620899289656904005241147645957778658951624671769646864054090034425179657998244791 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P132)`. -/
def ampRadius2657P132 : ℚ := (3148432518132247995710946259307123 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P132 :
    compactExp2620 (ampArg2657P132 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P132, 0), ampRadius2657P132) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P132 :
    |Real.exp ((ampArg2657P132 : ℝ)) - (ampValue2657P132 : ℝ)|
      ≤ (ampRadius2657P132 : ℝ) := by
  have harg : ampArg2657P132 = (-66319058899973530498766796664177845372819510133473 / 2009564751329991512530066644984889152026907246592) := rfl
  have hsmall : |((ampArg2657P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P132 20 hsmall
  rw [ampChain2657P132] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
