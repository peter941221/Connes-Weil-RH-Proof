import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 053 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 053. -/
def ampArg2657P053 : ℚ := (-77331225117681523082534610964092170270358915633884225 / 2016324196402646938526758687336201960992815934603264)

/-- Stored center of the certified ball for `exp (ampArg2657P053)`. -/
def ampValue2657P053 : ℚ := (23564427610856839015636459618303646299982350615030880528179035077036210109013965 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P053)`. -/
def ampRadius2657P053 : ℚ := (933517331512077953498798236685 / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P053 :
    compactExp2620 (ampArg2657P053 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P053, 0), ampRadius2657P053) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P053 :
    |Real.exp ((ampArg2657P053 : ℝ)) - (ampValue2657P053 : ℝ)|
      ≤ (ampRadius2657P053 : ℝ) := by
  have harg : ampArg2657P053 = (-77331225117681523082534610964092170270358915633884225 / 2016324196402646938526758687336201960992815934603264) := rfl
  have hsmall : |((ampArg2657P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P053 20 hsmall
  rw [ampChain2657P053] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
