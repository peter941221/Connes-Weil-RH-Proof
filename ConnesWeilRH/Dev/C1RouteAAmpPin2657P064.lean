import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 064 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 064. -/
def ampArg2657P064 : ℚ := (-76502372939502945860034432279878673625598261556676175 / 2209242412530326123729645085254751319587399030276096)

/-- Stored center of the certified ball for `exp (ampArg2657P064)`. -/
def ampValue2657P064 : ℚ := (244127360274747179184265894333978530552233637834949791683890053596983837062652063 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P064)`. -/
def ampRadius2657P064 : ℚ := (309478415178842191286761247728989 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P064 :
    compactExp2620 (ampArg2657P064 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P064, 0), ampRadius2657P064) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P064 :
    |Real.exp ((ampArg2657P064 : ℝ)) - (ampValue2657P064 : ℝ)|
      ≤ (ampRadius2657P064 : ℝ) := by
  have harg : ampArg2657P064 = (-76502372939502945860034432279878673625598261556676175 / 2209242412530326123729645085254751319587399030276096) := rfl
  have hsmall : |((ampArg2657P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P064 20 hsmall
  rw [ampChain2657P064] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
