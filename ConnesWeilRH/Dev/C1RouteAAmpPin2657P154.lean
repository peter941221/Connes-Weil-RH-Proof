import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 154 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 154. -/
def ampArg2657P154 : ℚ := (-68313091522104074886574724478398873089784944761821675 / 1573489200291383354311042183023168206037068374081536)

/-- Stored center of the certified ball for `exp (ampArg2657P154)`. -/
def ampValue2657P154 : ℚ := (37290457811690095206108756367864322327392999355497618646696209666362292475683 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P154)`. -/
def ampRadius2657P154 : ℚ := (23636765355134676590009678427 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P154 :
    compactExp2620 (ampArg2657P154 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P154, 0), ampRadius2657P154) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P154 :
    |Real.exp ((ampArg2657P154 : ℝ)) - (ampValue2657P154 : ℝ)|
      ≤ (ampRadius2657P154 : ℝ) := by
  have harg : ampArg2657P154 = (-68313091522104074886574724478398873089784944761821675 / 1573489200291383354311042183023168206037068374081536) := rfl
  have hsmall : |((ampArg2657P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P154 20 hsmall
  rw [ampChain2657P154] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
