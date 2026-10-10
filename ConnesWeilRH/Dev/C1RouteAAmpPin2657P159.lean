import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 159 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 159. -/
def ampArg2657P159 : ℚ := (-205225148144061570821118561233488396355152449983906775 / 4267402093301570158289984250927456882017866033922048)

/-- Stored center of the certified ball for `exp (ampArg2657P159)`. -/
def ampValue2657P159 : ℚ := (1389180248475547836616947833473399244834459032756278446289072518733597579003 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P159)`. -/
def ampRadius2657P159 : ℚ := (1762284868861534823800204805 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P159 :
    compactExp2620 (ampArg2657P159 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P159, 0), ampRadius2657P159) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P159 :
    |Real.exp ((ampArg2657P159 : ℝ)) - (ampValue2657P159 : ℝ)|
      ≤ (ampRadius2657P159 : ℝ) := by
  have harg : ampArg2657P159 = (-205225148144061570821118561233488396355152449983906775 / 4267402093301570158289984250927456882017866033922048) := rfl
  have hsmall : |((ampArg2657P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P159 20 hsmall
  rw [ampChain2657P159] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
