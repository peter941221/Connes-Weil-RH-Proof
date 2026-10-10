import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 051 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 051. -/
def ampArg2657P051 : ℚ := (-232334159007713561350506909690749037902830240625764575 / 5924744950034814067532962851227721826307693537656832)

/-- Stored center of the certified ball for `exp (ampArg2657P051)`. -/
def ampValue2657P051 : ℚ := (9955339359044306918087806246153175088492924516090766685334508629299281747100991 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P051)`. -/
def ampRadius2657P051 : ℚ := (25240730170260451316958028890083 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P051 :
    compactExp2620 (ampArg2657P051 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P051, 0), ampRadius2657P051) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P051 :
    |Real.exp ((ampArg2657P051 : ℝ)) - (ampValue2657P051 : ℝ)|
      ≤ (ampRadius2657P051 : ℝ) := by
  have harg : ampArg2657P051 = (-232334159007713561350506909690749037902830240625764575 / 5924744950034814067532962851227721826307693537656832) := rfl
  have hsmall : |((ampArg2657P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P051 20 hsmall
  rw [ampChain2657P051] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
