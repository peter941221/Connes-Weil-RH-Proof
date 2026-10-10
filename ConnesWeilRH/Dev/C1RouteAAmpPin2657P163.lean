import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 163 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 163. -/
def ampArg2657P163 : ℚ := (-68570475309852462317891582844232903107646415824104725 / 1292880885923849994015934695141641866263129325830144)

/-- Stored center of the certified ball for `exp (ampArg2657P163)`. -/
def ampValue2657P163 : ℚ := (19766891531424893849162986368006471088464247716047417976656389729574105695 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P163)`. -/
def ampRadius2657P163 : ℚ := (6869157748608699695649917 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P163 :
    compactExp2620 (ampArg2657P163 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P163, 0), ampRadius2657P163) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P163 :
    |Real.exp ((ampArg2657P163 : ℝ)) - (ampValue2657P163 : ℝ)|
      ≤ (ampRadius2657P163 : ℝ) := by
  have harg : ampArg2657P163 = (-68570475309852462317891582844232903107646415824104725 / 1292880885923849994015934695141641866263129325830144) := rfl
  have hsmall : |((ampArg2657P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P163 20 hsmall
  rw [ampChain2657P163] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
