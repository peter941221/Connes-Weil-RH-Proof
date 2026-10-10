import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 034 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 034. -/
def ampArg2657P034 : ℚ := (-77827157466716476893026399398437381869452188750787675 / 1544259167544765295946968486368842545643949723222016)

/-- Stored center of the certified ball for `exp (ampArg2657P034)`. -/
def ampValue2657P034 : ℚ := (8649526711249193823038472399572186570627842900649675961464160921206265763 / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768)

/-- Stored radius of the certified ball for `exp (ampArg2657P034)`. -/
def ampRadius2657P034 : ℚ := (353301203018551470592052439 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P034 :
    compactExp2620 (ampArg2657P034 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P034, 0), ampRadius2657P034) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P034 :
    |Real.exp ((ampArg2657P034 : ℝ)) - (ampValue2657P034 : ℝ)|
      ≤ (ampRadius2657P034 : ℝ) := by
  have harg : ampArg2657P034 = (-77827157466716476893026399398437381869452188750787675 / 1544259167544765295946968486368842545643949723222016) := rfl
  have hsmall : |((ampArg2657P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P034 20 hsmall
  rw [ampChain2657P034] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
