import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 061 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 061. -/
def ampArg2657P061 : ℚ := (-76759793895927133628898684682806581982752539069887025 / 2162474360135737230347127170607830262958409188900864)

/-- Stored center of the certified ball for `exp (ampArg2657P061)`. -/
def ampValue2657P061 : ℚ := (409949520531541295567600033710364356800322944819102504604527420415767757425976709 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P061)`. -/
def ampRadius2657P061 : ℚ := (129922587294172273318043175660399 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P061 :
    compactExp2620 (ampArg2657P061 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P061, 0), ampRadius2657P061) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P061 :
    |Real.exp ((ampArg2657P061 : ℝ)) - (ampValue2657P061 : ℝ)|
      ≤ (ampRadius2657P061 : ℝ) := by
  have harg : ampArg2657P061 = (-76759793895927133628898684682806581982752539069887025 / 2162474360135737230347127170607830262958409188900864) := rfl
  have hsmall : |((ampArg2657P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P061 20 hsmall
  rw [ampChain2657P061] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
