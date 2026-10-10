import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 085 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 085. -/
def ampArg2657P085 : ℚ := (-74241467435751063442763095424173581537944262907725825 / 2413852641756652532278160961835030942339229586292736)

/-- Stored center of the certified ball for `exp (ampArg2657P085)`. -/
def ampValue2657P085 : ℚ := (46905612310380869388915868981697864545501366037534935166157746888162431208986812907 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P085)`. -/
def ampRadius2657P085 : ℚ := (59461671681432880539472286018082513 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P085 :
    compactExp2620 (ampArg2657P085 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P085, 0), ampRadius2657P085) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P085 :
    |Real.exp ((ampArg2657P085 : ℝ)) - (ampValue2657P085 : ℝ)|
      ≤ (ampRadius2657P085 : ℝ) := by
  have harg : ampArg2657P085 = (-74241467435751063442763095424173581537944262907725825 / 2413852641756652532278160961835030942339229586292736) := rfl
  have hsmall : |((ampArg2657P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P085 20 hsmall
  rw [ampChain2657P085] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
