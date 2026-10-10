import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 037 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 037. -/
def ampArg2657P037 : ℚ := (-3113748272784663087440143776579468497582970441055625 / 65219510565891542724839435659964129752145989730304)

/-- Stored center of the certified ball for `exp (ampArg2657P037)`. -/
def ampValue2657P037 : ℚ := (1968909533506049343653833372329726181810063649765171652437477103164210136959 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P037)`. -/
def ampRadius2657P037 : ℚ := (4994423840782394892307078993 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P037 :
    compactExp2620 (ampArg2657P037 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P037, 0), ampRadius2657P037) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P037 :
    |Real.exp ((ampArg2657P037 : ℝ)) - (ampValue2657P037 : ℝ)|
      ≤ (ampRadius2657P037 : ℝ) := by
  have harg : ampArg2657P037 = (-3113748272784663087440143776579468497582970441055625 / 65219510565891542724839435659964129752145989730304) := rfl
  have hsmall : |((ampArg2657P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P037 20 hsmall
  rw [ampChain2657P037] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
