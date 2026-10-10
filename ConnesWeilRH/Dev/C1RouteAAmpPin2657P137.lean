import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 137 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 137. -/
def ampArg2657P137 : ℚ := (-2750424466836363561663431183918701910399912621810625 / 79834526939200571906876283987126959948705315160064)

/-- Stored center of the certified ball for `exp (ampArg2657P137)`. -/
def ampValue2657P137 : ℚ := (36416119902447754148896702682129248986699794729725802117590530894354604890188513 / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384)

/-- Stored radius of the certified ball for `exp (ampArg2657P137)`. -/
def ampRadius2657P137 : ℚ := (46164433024107558770308731219561 / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P137 :
    compactExp2620 (ampArg2657P137 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P137, 0), ampRadius2657P137) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P137 :
    |Real.exp ((ampArg2657P137 : ℝ)) - (ampValue2657P137 : ℝ)|
      ≤ (ampRadius2657P137 : ℝ) := by
  have harg : ampArg2657P137 = (-2750424466836363561663431183918701910399912621810625 / 79834526939200571906876283987126959948705315160064) := rfl
  have hsmall : |((ampArg2657P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P137 20 hsmall
  rw [ampChain2657P137] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
