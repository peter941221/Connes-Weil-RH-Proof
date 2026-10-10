import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 160 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 160. -/
def ampArg2657P160 : ℚ := (-68441527881332141281594819656295474516077635942834575 / 1390801495625020489535581578933632828580076806209536)

/-- Stored center of the certified ball for `exp (ampArg2657P160)`. -/
def ampValue2657P160 : ℚ := (113453788428646816499366127507948862152263700979619157874944664883166935199 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P160)`. -/
def ampRadius2657P160 : ℚ := (1153029953103344107579433023 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P160 :
    compactExp2620 (ampArg2657P160 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P160, 0), ampRadius2657P160) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P160 :
    |Real.exp ((ampArg2657P160 : ℝ)) - (ampValue2657P160 : ℝ)|
      ≤ (ampRadius2657P160 : ℝ) := by
  have harg : ampArg2657P160 = (-68441527881332141281594819656295474516077635942834575 / 1390801495625020489535581578933632828580076806209536) := rfl
  have hsmall : |((ampArg2657P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P160 20 hsmall
  rw [ampChain2657P160] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
