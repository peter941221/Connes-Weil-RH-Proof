import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 083 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 083. -/
def ampArg2657P083 : ℚ := (-74481038135622139104491361512766417449728242362860725 / 2403622130295336211850735168006016961201638058491904)

/-- Stored center of the certified ball for `exp (ampArg2657P083)`. -/
def ampValue2657P083 : ℚ := (37246515824035903072387344207516779572230971761856300495262637619325027168724874823 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P083)`. -/
def ampRadius2657P083 : ℚ := (47216963453706891105896259437389151 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P083 :
    compactExp2620 (ampArg2657P083 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P083, 0), ampRadius2657P083) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P083 :
    |Real.exp ((ampArg2657P083 : ℝ)) - (ampValue2657P083 : ℝ)|
      ≤ (ampRadius2657P083 : ℝ) := by
  have harg : ampArg2657P083 = (-74481038135622139104491361512766417449728242362860725 / 2403622130295336211850735168006016961201638058491904) := rfl
  have hsmall : |((ampArg2657P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P083 20 hsmall
  rw [ampChain2657P083] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
