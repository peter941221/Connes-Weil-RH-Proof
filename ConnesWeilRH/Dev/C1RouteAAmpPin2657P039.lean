import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 039 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 039. -/
def ampArg2657P039 : ℚ := (-233499731512136346499236518917679879785947735270644775 / 5056612977460257734119974060594249712632069607129088)

/-- Stored center of the certified ball for `exp (ampArg2657P039)`. -/
def ampValue2657P039 : ℚ := (18842484710267127644155456075850799830761915422595503811640745821895069153921 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P039)`. -/
def ampRadius2657P039 : ℚ := (746536150107476511027165229 / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P039 :
    compactExp2620 (ampArg2657P039 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P039, 0), ampRadius2657P039) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P039 :
    |Real.exp ((ampArg2657P039 : ℝ)) - (ampValue2657P039 : ℝ)|
      ≤ (ampRadius2657P039 : ℝ) := by
  have harg : ampArg2657P039 = (-233499731512136346499236518917679879785947735270644775 / 5056612977460257734119974060594249712632069607129088) := rfl
  have hsmall : |((ampArg2657P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P039 20 hsmall
  rw [ampChain2657P039] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
