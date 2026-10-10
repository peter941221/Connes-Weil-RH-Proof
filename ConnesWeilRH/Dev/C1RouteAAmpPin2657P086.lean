import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 086 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 086. -/
def ampArg2657P086 : ℚ := (-74120585609879415654250838285607752572914482877788275 / 2418237146668645241032772016333179791398197383921664)

/-- Stored center of the certified ball for `exp (ampArg2657P086)`. -/
def ampValue2657P086 : ℚ := (26068878024056194472789779092610694552078009601052376894300916899028992179717456653 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P086)`. -/
def ampRadius2657P086 : ℚ := (132188779421723361845427203887524825 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P086 :
    compactExp2620 (ampArg2657P086 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P086, 0), ampRadius2657P086) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P086 :
    |Real.exp ((ampArg2657P086 : ℝ)) - (ampValue2657P086 : ℝ)|
      ≤ (ampRadius2657P086 : ℝ) := by
  have harg : ampArg2657P086 = (-74120585609879415654250838285607752572914482877788275 / 2418237146668645241032772016333179791398197383921664) := rfl
  have hsmall : |((ampArg2657P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P086 20 hsmall
  rw [ampChain2657P086] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
