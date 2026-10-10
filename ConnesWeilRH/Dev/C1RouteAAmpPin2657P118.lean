import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 118 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 118. -/
def ampArg2657P118 : ℚ := (-70324325738336139913613465665249690562834810916007475 / 2301317015682173007576477229715877149825722780483584)

/-- Stored center of the certified ball for `exp (ampArg2657P118)`. -/
def ampValue2657P118 : ℚ := (28591664961441167487601877562143217123779963204088195205050350194162934785593092171 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P118)`. -/
def ampRadius2657P118 : ℚ := (18122648759776321844570815663637339 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P118 :
    compactExp2620 (ampArg2657P118 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P118, 0), ampRadius2657P118) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P118 :
    |Real.exp ((ampArg2657P118 : ℝ)) - (ampValue2657P118 : ℝ)|
      ≤ (ampRadius2657P118 : ℝ) := by
  have harg : ampArg2657P118 = (-70324325738336139913613465665249690562834810916007475 / 2301317015682173007576477229715877149825722780483584) := rfl
  have hsmall : |((ampArg2657P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P118 20 hsmall
  rw [ampChain2657P118] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
