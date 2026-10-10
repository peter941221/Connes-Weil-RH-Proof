import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 032 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 032. -/
def ampArg2657P032 : ℚ := (-124470018258415797770708571311340310423784948147455 / 2374940160662717242080987853163959906940890382336)

/-- Stored center of the certified ball for `exp (ampArg2657P032)`. -/
def ampValue2657P032 : ℚ := (1156601484266046796288038487219490836439211289548243940270165928130364447 / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768)

/-- Stored radius of the certified ball for `exp (ampArg2657P032)`. -/
def ampRadius2657P032 : ℚ := (24668763408052848951490475 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P032 :
    compactExp2620 (ampArg2657P032 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P032, 0), ampRadius2657P032) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P032 :
    |Real.exp ((ampArg2657P032 : ℝ)) - (ampValue2657P032 : ℝ)|
      ≤ (ampRadius2657P032 : ℝ) := by
  have harg : ampArg2657P032 = (-124470018258415797770708571311340310423784948147455 / 2374940160662717242080987853163959906940890382336) := rfl
  have hsmall : |((ampArg2657P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P032 20 hsmall
  rw [ampChain2657P032] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
