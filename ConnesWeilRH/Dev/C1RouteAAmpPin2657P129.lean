import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 129 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 129. -/
def ampArg2657P129 : ℚ := (-207928333013330619799218393978525317272733609835481275 / 6437732024737960991822456227511137166206925860241408)

/-- Stored center of the certified ball for `exp (ampArg2657P129)`. -/
def ampValue2657P129 : ℚ := (20071933400105070404870388463552182404047609632821985994564197865910116684862963205 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P129)`. -/
def ampRadius2657P129 : ℚ := (25444982172586118549558544665795467 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P129 :
    compactExp2620 (ampArg2657P129 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P129, 0), ampRadius2657P129) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P129 :
    |Real.exp ((ampArg2657P129 : ℝ)) - (ampValue2657P129 : ℝ)|
      ≤ (ampRadius2657P129 : ℝ) := by
  have harg : ampArg2657P129 = (-207928333013330619799218393978525317272733609835481275 / 6437732024737960991822456227511137166206925860241408) := rfl
  have hsmall : |((ampArg2657P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P129 20 hsmall
  rw [ampChain2657P129] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
