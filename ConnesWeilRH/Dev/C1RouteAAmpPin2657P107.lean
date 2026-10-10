import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 107 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 107. -/
def ampArg2657P107 : ℚ := (-114480936637075081908561102331536625482051261301205 / 3836441797993620160284672685880242926596822925312)

/-- Stored center of the certified ball for `exp (ampArg2657P107)`. -/
def ampValue2657P107 : ℚ := (14654127673483829654359113789589964302366787292513096929284542706651272533315549823 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P107)`. -/
def ampRadius2657P107 : ℚ := (74307369575413328339730392044502593 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P107 :
    compactExp2620 (ampArg2657P107 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P107, 0), ampRadius2657P107) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P107 :
    |Real.exp ((ampArg2657P107 : ℝ)) - (ampValue2657P107 : ℝ)|
      ≤ (ampRadius2657P107 : ℝ) := by
  have harg : ampArg2657P107 = (-114480936637075081908561102331536625482051261301205 / 3836441797993620160284672685880242926596822925312) := rfl
  have hsmall : |((ampArg2657P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P107 20 hsmall
  rw [ampChain2657P107] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
