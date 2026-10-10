import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 150 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 150. -/
def ampArg2657P150 : ℚ := (-204950759687134528961868930897205026110832027622155225 / 5056612977460257734119974060594249712632069607129088)

/-- Stored center of the certified ball for `exp (ampArg2657P150)`. -/
def ampValue2657P150 : ℚ := (5334671702470997683630413735602773945670682040364929347720602898356683797301837 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P150)`. -/
def ampRadius2657P150 : ℚ := (845345450437107497065885280603 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P150 :
    compactExp2620 (ampArg2657P150 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P150, 0), ampRadius2657P150) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P150 :
    |Real.exp ((ampArg2657P150 : ℝ)) - (ampValue2657P150 : ℝ)|
      ≤ (ampRadius2657P150 : ℝ) := by
  have harg : ampArg2657P150 = (-204950759687134528961868930897205026110832027622155225 / 5056612977460257734119974060594249712632069607129088) := rfl
  have hsmall : |((ampArg2657P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P150 20 hsmall
  rw [ampChain2657P150] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
