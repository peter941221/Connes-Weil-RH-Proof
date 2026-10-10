import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 131 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 131. -/
def ampArg2657P131 : ℚ := (-69155361592246573963684150553502450219248727623965525 / 2111321802829155628209998201462760357270451549896704)

/-- Stored center of the certified ball for `exp (ampArg2657P131)`. -/
def ampValue2657P131 : ℚ := (1589993283293465728419838298289548879751068499650371957499969932937809386596480331 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P131)`. -/
def ampRadius2657P131 : ℚ := (8062475605800932265896331335315149 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P131 :
    compactExp2620 (ampArg2657P131 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P131, 0), ampRadius2657P131) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P131 :
    |Real.exp ((ampArg2657P131 : ℝ)) - (ampValue2657P131 : ℝ)|
      ≤ (ampRadius2657P131 : ℝ) := by
  have harg : ampArg2657P131 = (-69155361592246573963684150553502450219248727623965525 / 2111321802829155628209998201462760357270451549896704) := rfl
  have hsmall : |((ampArg2657P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P131 20 hsmall
  rw [ampChain2657P131] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
