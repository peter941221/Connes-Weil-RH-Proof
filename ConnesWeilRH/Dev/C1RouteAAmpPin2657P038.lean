import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 038 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 038. -/
def ampArg2657P038 : ℚ := (-77840575358680398747635646789327462354155317535723475 / 1658256295256575723566855903320712621177112461574144)

/-- Stored center of the certified ball for `exp (ampArg2657P038)`. -/
def ampValue2657P038 : ℚ := (4387885932023153939068067165871396711964849079662639199924831415982708293379 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P038)`. -/
def ampRadius2657P038 : ℚ := (5563764172599276174173899121 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P038 :
    compactExp2620 (ampArg2657P038 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P038, 0), ampRadius2657P038) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P038 :
    |Real.exp ((ampArg2657P038 : ℝ)) - (ampValue2657P038 : ℝ)|
      ≤ (ampRadius2657P038 : ℝ) := by
  have harg : ampArg2657P038 = (-77840575358680398747635646789327462354155317535723475 / 1658256295256575723566855903320712621177112461574144) := rfl
  have hsmall : |((ampArg2657P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P038 20 hsmall
  rw [ampChain2657P038] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
