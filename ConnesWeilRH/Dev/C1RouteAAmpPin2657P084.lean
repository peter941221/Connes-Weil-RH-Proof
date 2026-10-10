import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 084 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 084. -/
def ampArg2657P084 : ℚ := (-223084929170347514453624597573867166169232161110105525 / 7226942908896648567652446037177929996821129433448448)

/-- Stored center of the certified ball for `exp (ampArg2657P084)`. -/
def ampValue2657P084 : ℚ := (41932125700479248499941805737596443510805198867785719065983145542237205321129318611 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P084)`. -/
def ampRadius2657P084 : ℚ := (53156849149199890013047713260863407 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P084 :
    compactExp2620 (ampArg2657P084 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P084, 0), ampRadius2657P084) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P084 :
    |Real.exp ((ampArg2657P084 : ℝ)) - (ampValue2657P084 : ℝ)|
      ≤ (ampRadius2657P084 : ℝ) := by
  have harg : ampArg2657P084 = (-223084929170347514453624597573867166169232161110105525 / 7226942908896648567652446037177929996821129433448448) := rfl
  have hsmall : |((ampArg2657P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P084 20 hsmall
  rw [ampChain2657P084] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
