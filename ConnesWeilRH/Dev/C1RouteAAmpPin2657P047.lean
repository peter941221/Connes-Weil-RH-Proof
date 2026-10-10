import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 047 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 047. -/
def ampArg2657P047 : ℚ := (-3105292399040086295408000337722146308469502854981125 / 75450022027207863152265229488978110889737517531136)

/-- Stored center of the certified ball for `exp (ampArg2657P047)`. -/
def ampValue2657P047 : ℚ := (2853412449685453155078689193889042969740166996647167511436537477804970875168705 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P047)`. -/
def ampRadius2657P047 : ℚ := (226079649918451689707871947167 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P047 :
    compactExp2620 (ampArg2657P047 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P047, 0), ampRadius2657P047) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P047 :
    |Real.exp ((ampArg2657P047 : ℝ)) - (ampValue2657P047 : ℝ)|
      ≤ (ampRadius2657P047 : ℝ) := by
  have harg : ampArg2657P047 = (-3105292399040086295408000337722146308469502854981125 / 75450022027207863152265229488978110889737517531136) := rfl
  have hsmall : |((ampArg2657P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P047 20 hsmall
  rw [ampChain2657P047] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
