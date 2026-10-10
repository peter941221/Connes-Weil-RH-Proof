import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 123 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 123. -/
def ampArg2657P123 : ℚ := (-209492595318725725650070142092942165580139500357408175 / 6713955834193501643362952660894514656921897110863872)

/-- Stored center of the certified ball for `exp (ampArg2657P123)`. -/
def ampValue2657P123 : ℚ := (7506023676050949407434486705195456744757709990281830334163597365205762484278491791 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P123)`. -/
def ampRadius2657P123 : ℚ := (76122388494755939706255719574444561 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P123 :
    compactExp2620 (ampArg2657P123 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P123, 0), ampRadius2657P123) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P123 :
    |Real.exp ((ampArg2657P123 : ℝ)) - (ampValue2657P123 : ℝ)|
      ≤ (ampRadius2657P123 : ℝ) := by
  have harg : ampArg2657P123 = (-209492595318725725650070142092942165580139500357408175 / 6713955834193501643362952660894514656921897110863872) := rfl
  have hsmall : |((ampArg2657P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P123 20 hsmall
  rw [ampChain2657P123] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
