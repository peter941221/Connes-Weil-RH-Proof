import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 125 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 125. -/
def ampArg2657P125 : ℚ := (-69647790793587345960334050991749628339994992740923825 / 2209242412530326123729645085254751319587399030276096)

/-- Stored center of the certified ball for `exp (ampArg2657P125)`. -/
def ampValue2657P125 : ℚ := (10867388664676398839432665959392712897138934501748238759027239958017856666517760993 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P125)`. -/
def ampRadius2657P125 : ℚ := (27552931900474231885082447688167957 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P125 :
    compactExp2620 (ampArg2657P125 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P125, 0), ampRadius2657P125) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P125 :
    |Real.exp ((ampArg2657P125 : ℝ)) - (ampValue2657P125 : ℝ)|
      ≤ (ampRadius2657P125 : ℝ) := by
  have harg : ampArg2657P125 = (-69647790793587345960334050991749628339994992740923825 / 2209242412530326123729645085254751319587399030276096) := rfl
  have hsmall : |((ampArg2657P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P125 20 hsmall
  rw [ampChain2657P125] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
