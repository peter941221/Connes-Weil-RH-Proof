import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 151 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 151. -/
def ampArg2657P151 : ℚ := (-68309588374409893072732836482300839611437936761876525 / 1658256295256575723566855903320712621177112461574144)

/-- Stored center of the certified ball for `exp (ampArg2657P151)`. -/
def ampValue2657P151 : ℚ := (2750644611016260526189275029893309844236762418227310344304069788615443895167825 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P151)`. -/
def ampRadius2657P151 : ℚ := (3486995694915504377597591439567 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P151 :
    compactExp2620 (ampArg2657P151 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P151, 0), ampRadius2657P151) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P151 :
    |Real.exp ((ampArg2657P151 : ℝ)) - (ampValue2657P151 : ℝ)|
      ≤ (ampRadius2657P151 : ℝ) := by
  have harg : ampArg2657P151 = (-68309588374409893072732836482300839611437936761876525 / 1658256295256575723566855903320712621177112461574144) := rfl
  have hsmall : |((ampArg2657P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P151 20 hsmall
  rw [ampChain2657P151] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
