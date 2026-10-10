import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 052 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 052. -/
def ampArg2657P052 : ℚ := (-3095582082487248111151308146946430168223817550093375 / 79834526939200571906876283987126959948705315160064)

/-- Stored center of the certified ball for `exp (ampArg2657P052)`. -/
def ampValue2657P052 : ℚ := (3861440393292264952569741085897195623436122494016994294149961023233479617299975 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P052)`. -/
def ampRadius2657P052 : ℚ := (4895138547042158590411929639695 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P052 :
    compactExp2620 (ampArg2657P052 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P052, 0), ampRadius2657P052) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P052 :
    |Real.exp ((ampArg2657P052 : ℝ)) - (ampValue2657P052 : ℝ)|
      ≤ (ampRadius2657P052 : ℝ) := by
  have harg : ampArg2657P052 = (-3095582082487248111151308146946430168223817550093375 / 79834526939200571906876283987126959948705315160064) := rfl
  have hsmall : |((ampArg2657P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P052 20 hsmall
  rw [ampChain2657P052] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
