import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 124 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 124. -/
def ampArg2657P124 : ℚ := (-69738231473978517297530591750429097424216289460993175 / 2223857428903635152911681933581914149783958355705856)

/-- Stored center of the certified ball for `exp (ampArg2657P124)`. -/
def ampValue2657P124 : ℚ := (3209091119580652672243389522825442707639965737611904736294980471689707672362575195 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P124)`. -/
def ampRadius2657P124 : ℚ := (65090047124790802641414960059335779 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P124 :
    compactExp2620 (ampArg2657P124 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P124, 0), ampRadius2657P124) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P124 :
    |Real.exp ((ampArg2657P124 : ℝ)) - (ampValue2657P124 : ℝ)|
      ≤ (ampRadius2657P124 : ℝ) := by
  have harg : ampArg2657P124 = (-69738231473978517297530591750429097424216289460993175 / 2223857428903635152911681933581914149783958355705856) := rfl
  have hsmall : |((ampArg2657P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P124 20 hsmall
  rw [ampChain2657P124] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
