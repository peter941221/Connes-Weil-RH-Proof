import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 080 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 080. -/
def ampArg2657P080 : ℚ := (-74833796745474192682421319061492266092931066505878575 / 2384622609010034473914087265180705281946110935433216)

/-- Stored center of the certified ball for `exp (ampArg2657P080)`. -/
def ampValue2657P080 : ℚ := (50193501007726928290479047147452467327134311848741566794718048164059069835068829277 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P080)`. -/
def ampRadius2657P080 : ℚ := (31814862983308495125120427657387473 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P080 :
    compactExp2620 (ampArg2657P080 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P080, 0), ampRadius2657P080) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P080 :
    |Real.exp ((ampArg2657P080 : ℝ)) - (ampValue2657P080 : ℝ)|
      ≤ (ampRadius2657P080 : ℝ) := by
  have harg : ampArg2657P080 = (-74833796745474192682421319061492266092931066505878575 / 2384622609010034473914087265180705281946110935433216) := rfl
  have hsmall : |((ampArg2657P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P080 20 hsmall
  rw [ampChain2657P080] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
