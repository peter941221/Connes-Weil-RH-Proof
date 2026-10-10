import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 042 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 042. -/
def ampArg2657P042 : ℚ := (-9334415074175677237986777013738260647695725965183625 / 211735049708314560274758840139771502472653227163648)

/-- Stored center of the certified ball for `exp (ampArg2657P042)`. -/
def ampValue2657P042 : ℚ := (38151508617678486403301394305003057299402271806932950180921701709439787388759 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P042)`. -/
def ampRadius2657P042 : ℚ := (96730841248840967225180752311 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P042 :
    compactExp2620 (ampArg2657P042 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P042, 0), ampRadius2657P042) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P042 :
    |Real.exp ((ampArg2657P042 : ℝ)) - (ampValue2657P042 : ℝ)|
      ≤ (ampRadius2657P042 : ℝ) := by
  have harg : ampArg2657P042 = (-9334415074175677237986777013738260647695725965183625 / 211735049708314560274758840139771502472653227163648) := rfl
  have hsmall : |((ampArg2657P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P042 20 hsmall
  rw [ampChain2657P042] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
