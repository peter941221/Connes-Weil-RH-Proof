import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 050 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 050. -/
def ampArg2657P050 : ℚ := (-77496653601499875421598621559671188877817227100790075 / 1953479625997418113044000239529401791147610835255296)

/-- Stored center of the certified ball for `exp (ampArg2657P050)`. -/
def ampValue2657P050 : ℚ := (12608572014410793499809229340354127532101790989398281396990098671589730001115167 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P050)`. -/
def ampRadius2657P050 : ℚ := (15983871010893824069547089775803 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P050 :
    compactExp2620 (ampArg2657P050 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P050, 0), ampRadius2657P050) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P050 :
    |Real.exp ((ampArg2657P050 : ℝ)) - (ampValue2657P050 : ℝ)|
      ≤ (ampRadius2657P050 : ℝ) := by
  have harg : ampArg2657P050 = (-77496653601499875421598621559671188877817227100790075 / 1953479625997418113044000239529401791147610835255296) := rfl
  have hsmall : |((ampArg2657P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P050 20 hsmall
  rw [ampChain2657P050] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
