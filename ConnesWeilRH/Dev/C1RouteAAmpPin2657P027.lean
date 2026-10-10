import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 027 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 027. -/
def ampArg2657P027 : ℚ := (-9315319666983253823013090456758263836016411801026375 / 159120990764402055219426186161985313765039655616512)

/-- Stored center of the certified ball for `exp (ampArg2657P027)`. -/
def ampValue2657P027 : ℚ := (80347254966811835451246717886681621726133303231479477321470077683407527 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P027)`. -/
def ampRadius2657P027 : ℚ := (2519709571821174284916271 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P027 :
    compactExp2620 (ampArg2657P027 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P027, 0), ampRadius2657P027) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P027 :
    |Real.exp ((ampArg2657P027 : ℝ)) - (ampValue2657P027 : ℝ)|
      ≤ (ampRadius2657P027 : ℝ) := by
  have harg : ampArg2657P027 = (-9315319666983253823013090456758263836016411801026375 / 159120990764402055219426186161985313765039655616512) := rfl
  have hsmall : |((ampArg2657P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P027 20 hsmall
  rw [ampChain2657P027] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
