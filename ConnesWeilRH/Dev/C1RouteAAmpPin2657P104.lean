import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 104 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 104. -/
def ampArg2657P104 : ℚ := (-71908696297339228377605387847454720427648991389874175 / 2413852641756652532278160961835030942339229586292736)

/-- Stored center of the certified ball for `exp (ampArg2657P104)`. -/
def ampValue2657P104 : ℚ := (15411372518059346874807414634444542570930875876057040746653134525185187326809243807 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P104)`. -/
def ampRadius2657P104 : ℚ := (156294325237814433562919489365667197 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P104 :
    compactExp2620 (ampArg2657P104 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P104, 0), ampRadius2657P104) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P104 :
    |Real.exp ((ampArg2657P104 : ℝ)) - (ampValue2657P104 : ℝ)|
      ≤ (ampRadius2657P104 : ℝ) := by
  have harg : ampArg2657P104 = (-71908696297339228377605387847454720427648991389874175 / 2413852641756652532278160961835030942339229586292736) := rfl
  have hsmall : |((ampArg2657P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P104 20 hsmall
  rw [ampChain2657P104] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
