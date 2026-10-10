import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 062 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 062. -/
def ampArg2657P062 : ℚ := (-3067055123810489043526384677394804760994866463006875 / 87142035125855086497894708150708375046984977874944)

/-- Stored center of the certified ball for `exp (ampArg2657P062)`. -/
def ampValue2657P062 : ℚ := (1107005594498720220935204668064997623831371074086266304962795224857157519517915097 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P062)`. -/
def ampRadius2657P062 : ℚ := (1403343411964940200850907318586265 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P062 :
    compactExp2620 (ampArg2657P062 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P062, 0), ampRadius2657P062) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P062 :
    |Real.exp ((ampArg2657P062 : ℝ)) - (ampValue2657P062 : ℝ)|
      ≤ (ampRadius2657P062 : ℝ) := by
  have harg : ampArg2657P062 = (-3067055123810489043526384677394804760994866463006875 / 87142035125855086497894708150708375046984977874944) := rfl
  have hsmall : |((ampArg2657P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P062 20 hsmall
  rw [ampChain2657P062] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
