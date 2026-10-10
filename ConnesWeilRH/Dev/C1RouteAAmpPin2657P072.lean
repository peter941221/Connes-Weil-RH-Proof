import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 072 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 072. -/
def ampArg2657P072 : ℚ := (-9086592928276926640737034690304433412908714404077125 / 277502623388205191593924657612004238357170191597568)

/-- Stored center of the certified ball for `exp (ampArg2657P072)`. -/
def ampValue2657P072 : ℚ := (12852467005826444950246639494647617652113935812171841534952707328213135555760034713 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P072)`. -/
def ampRadius2657P072 : ℚ := (16292946293112242486423278837886423 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P072 :
    compactExp2620 (ampArg2657P072 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P072, 0), ampRadius2657P072) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P072 :
    |Real.exp ((ampArg2657P072 : ℝ)) - (ampValue2657P072 : ℝ)|
      ≤ (ampRadius2657P072 : ℝ) := by
  have harg : ampArg2657P072 = (-9086592928276926640737034690304433412908714404077125 / 277502623388205191593924657612004238357170191597568) := rfl
  have hsmall : |((ampArg2657P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P072 20 hsmall
  rw [ampChain2657P072] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
