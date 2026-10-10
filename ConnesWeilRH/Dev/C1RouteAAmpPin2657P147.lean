import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 147 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 147. -/
def ampArg2657P147 : ℚ := (-8203604573795157780457440978857135588175464550528375 / 211735049708314560274758840139771502472653227163648)

/-- Stored center of the certified ball for `exp (ampArg2657P147)`. -/
def ampValue2657P147 : ℚ := (7960536701027155403689629476364859437401816097819289807275094586960056629877865 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P147)`. -/
def ampRadius2657P147 : ℚ := (40366210422248394683514021919529 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P147 :
    compactExp2620 (ampArg2657P147 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P147, 0), ampRadius2657P147) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P147 :
    |Real.exp ((ampArg2657P147 : ℝ)) - (ampValue2657P147 : ℝ)|
      ≤ (ampRadius2657P147 : ℝ) := by
  have harg : ampArg2657P147 = (-8203604573795157780457440978857135588175464550528375 / 211735049708314560274758840139771502472653227163648) := rfl
  have hsmall : |((ampArg2657P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P147 20 hsmall
  rw [ampChain2657P147] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
