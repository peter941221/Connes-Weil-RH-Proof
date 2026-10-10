import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 126 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 126. -/
def ampArg2657P126 : ℚ := (-208678852207259985640585639487390213857904668582350825 / 6582420686833720380724621025950049185152863181996032)

/-- Stored center of the certified ball for `exp (ampArg2657P126)`. -/
def ampValue2657P126 : ℚ := (4553131780252665697934483180577915441374725359665086216663717089506930976952904183 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P126)`. -/
def ampRadius2657P126 : ℚ := (23087818960029461629290303229306551 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P126 :
    compactExp2620 (ampArg2657P126 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P126, 0), ampRadius2657P126) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P126 :
    |Real.exp ((ampArg2657P126 : ℝ)) - (ampValue2657P126 : ℝ)|
      ≤ (ampRadius2657P126 : ℝ) := by
  have harg : ampArg2657P126 = (-208678852207259985640585639487390213857904668582350825 / 6582420686833720380724621025950049185152863181996032) := rfl
  have hsmall : |((ampArg2657P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P126 20 hsmall
  rw [ampChain2657P126] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
