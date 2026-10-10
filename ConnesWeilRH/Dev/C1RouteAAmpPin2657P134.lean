import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 134 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 134. -/
def ampArg2657P134 : ℚ := (-68944773167330811504536384888861249371030578279782675 / 2055784740610581317318258177819541602523526113263616)

/-- Stored center of the certified ball for `exp (ampArg2657P134)`. -/
def ampValue2657P134 : ℚ := (363547717827859164346975557303954605810972888437799500456540983256150969965285449 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P134)`. -/
def ampRadius2657P134 : ℚ := (7373859562750833170424869385769635 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P134 :
    compactExp2620 (ampArg2657P134 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P134, 0), ampRadius2657P134) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P134 :
    |Real.exp ((ampArg2657P134 : ℝ)) - (ampValue2657P134 : ℝ)|
      ≤ (ampRadius2657P134 : ℝ) := by
  have harg : ampArg2657P134 = (-68944773167330811504536384888861249371030578279782675 / 2055784740610581317318258177819541602523526113263616) := rfl
  have hsmall : |((ampArg2657P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P134 20 hsmall
  rw [ampChain2657P134] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
