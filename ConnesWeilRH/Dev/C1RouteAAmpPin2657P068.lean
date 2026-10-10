import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 068 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 068. -/
def ampArg2657P068 : ℚ := (-76127749856111343719849932410678891893402042655379975 / 2264779474748900434621385108897970074334324466909184)

/-- Stored center of the certified ball for `exp (ampArg2657P068)`. -/
def ampValue2657P068 : ℚ := (5386775408686588543888301950161484199376004516827601328183247487252500472959834261 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P068)`. -/
def ampRadius2657P068 : ℚ := (6828767985958668119921701896122913 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P068 :
    compactExp2620 (ampArg2657P068 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P068, 0), ampRadius2657P068) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P068 :
    |Real.exp ((ampArg2657P068 : ℝ)) - (ampValue2657P068 : ℝ)|
      ≤ (ampRadius2657P068 : ℝ) := by
  have harg : ampArg2657P068 = (-76127749856111343719849932410678891893402042655379975 / 2264779474748900434621385108897970074334324466909184) := rfl
  have hsmall : |((ampArg2657P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P068 20 hsmall
  rw [ampChain2657P068] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
