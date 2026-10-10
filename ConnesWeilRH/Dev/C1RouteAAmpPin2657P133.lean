import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 133 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 133. -/
def ampArg2657P133 : ℚ := (-69012132100049973224801228612242269754419068973688225 / 2074784261895883055254906080644853281779053236322304)

/-- Stored center of the certified ball for `exp (ampArg2657P133)`. -/
def ampValue2657P133 : ℚ := (3827611325868183480135621746744917237053061841698363461838129089081129358530766125 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P133)`. -/
def ampRadius2657P133 : ℚ := (1213056928246539683420940381321955 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P133 :
    compactExp2620 (ampArg2657P133 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P133, 0), ampRadius2657P133) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P133 :
    |Real.exp ((ampArg2657P133 : ℝ)) - (ampValue2657P133 : ℝ)|
      ≤ (ampRadius2657P133 : ℝ) := by
  have harg : ampArg2657P133 = (-69012132100049973224801228612242269754419068973688225 / 2074784261895883055254906080644853281779053236322304) := rfl
  have hsmall : |((ampArg2657P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P133 20 hsmall
  rw [ampChain2657P133] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
