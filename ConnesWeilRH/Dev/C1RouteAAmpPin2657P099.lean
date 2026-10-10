import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 099 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 099. -/
def ampArg2657P099 : ℚ := (-217556042184202553856827337313096848440156577536195775 / 7292710482576539198971611854650162732705646397882368)

/-- Stored center of the certified ball for `exp (ampArg2657P099)`. -/
def ampValue2657P099 : ℚ := (236445689368162527005609298436364505326312537723138280251277321041105771342359747253 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P099)`. -/
def ampRadius2657P099 : ℚ := (37467380938225486152693183692186681 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P099 :
    compactExp2620 (ampArg2657P099 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P099, 0), ampRadius2657P099) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P099 :
    |Real.exp ((ampArg2657P099 : ℝ)) - (ampValue2657P099 : ℝ)|
      ≤ (ampRadius2657P099 : ℝ) := by
  have harg : ampArg2657P099 = (-217556042184202553856827337313096848440156577536195775 / 7292710482576539198971611854650162732705646397882368) := rfl
  have hsmall : |((ampArg2657P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P099 20 hsmall
  rw [ampChain2657P099] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
