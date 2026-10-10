import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 069 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 069. -/
def ampArg2657P069 : ℚ := (-228086950177022690316111382028912024422776302782450275 / 6832337466817304779737451132344533581514027646844928)

/-- Stored center of the certified ball for `exp (ampArg2657P069)`. -/
def ampValue2657P069 : ℚ := (3390965886650986065709716210331532712124411530338551350731305343126164879612380849 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P069)`. -/
def ampRadius2657P069 : ℚ := (8597393595832860655791624679179015 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P069 :
    compactExp2620 (ampArg2657P069 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P069, 0), ampRadius2657P069) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P069 :
    |Real.exp ((ampArg2657P069 : ℝ)) - (ampValue2657P069 : ℝ)|
      ≤ (ampRadius2657P069 : ℝ) := by
  have harg : ampArg2657P069 = (-228086950177022690316111382028912024422776302782450275 / 6832337466817304779737451132344533581514027646844928) := rfl
  have hsmall : |((ampArg2657P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P069 20 hsmall
  rw [ampChain2657P069] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
