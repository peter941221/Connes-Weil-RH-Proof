import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 149 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 149. -/
def ampArg2657P149 : ℚ := (-68328377140026963702940522233256340123951597705879425 / 1712331855837819131540392242131215092904381965664256)

/-- Stored center of the certified ball for `exp (ampArg2657P149)`. -/
def ampValue2657P149 : ℚ := (78060586064686081272393913770830855978119944952982265381411821164558610496109 / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192)

/-- Stored radius of the certified ball for `exp (ampArg2657P149)`. -/
def ampRadius2657P149 : ℚ := (12666538679136232771761074514463 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P149 :
    compactExp2620 (ampArg2657P149 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P149, 0), ampRadius2657P149) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P149 :
    |Real.exp ((ampArg2657P149 : ℝ)) - (ampValue2657P149 : ℝ)|
      ≤ (ampRadius2657P149 : ℝ) := by
  have harg : ampArg2657P149 = (-68328377140026963702940522233256340123951597705879425 / 1712331855837819131540392242131215092904381965664256) := rfl
  have hsmall : |((ampArg2657P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P149 20 hsmall
  rw [ampChain2657P149] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
