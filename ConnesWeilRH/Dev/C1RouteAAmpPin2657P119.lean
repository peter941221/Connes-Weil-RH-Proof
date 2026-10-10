import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 119 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 119. -/
def ampArg2657P119 : ℚ := (-70221842406985659211061256888153639547744224095330925 / 2289625002583525784230847751054146885668475320139776)

/-- Stored center of the certified ball for `exp (ampArg2657P119)`. -/
def ampValue2657P119 : ℚ := (6395113892355488864601308639874720521406617857752086688698821329111053469884842797 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P119)`. -/
def ampRadius2657P119 : ℚ := (16214014162054011395404198216319321 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P119 :
    compactExp2620 (ampArg2657P119 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P119, 0), ampRadius2657P119) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P119 :
    |Real.exp ((ampArg2657P119 : ℝ)) - (ampValue2657P119 : ℝ)|
      ≤ (ampRadius2657P119 : ℝ) := by
  have harg : ampArg2657P119 = (-70221842406985659211061256888153639547744224095330925 / 2289625002583525784230847751054146885668475320139776) := rfl
  have hsmall : |((ampArg2657P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P119 20 hsmall
  rw [ampChain2657P119] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
