import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 114 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 114. -/
def ampArg2657P114 : ℚ := (-212252954903544643860448852397637441914880183348671025 / 7029640187856976673694948584761231789167578540146688)

/-- Stored center of the certified ball for `exp (ampArg2657P114)`. -/
def ampValue2657P114 : ℚ := (82315398990327394330342124469984458493033839111356160110296925924038403162906795581 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P114)`. -/
def ampRadius2657P114 : ℚ := (208700339368940353797440928706979067 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P114 :
    compactExp2620 (ampArg2657P114 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P114, 0), ampRadius2657P114) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P114 :
    |Real.exp ((ampArg2657P114 : ℝ)) - (ampValue2657P114 : ℝ)|
      ≤ (ampRadius2657P114 : ℝ) := by
  have harg : ampArg2657P114 = (-212252954903544643860448852397637441914880183348671025 / 7029640187856976673694948584761231789167578540146688) := rfl
  have hsmall : |((ampArg2657P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P114 20 hsmall
  rw [ampChain2657P114] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
