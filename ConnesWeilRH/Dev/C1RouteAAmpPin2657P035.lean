import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 035 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 035. -/
def ampArg2657P035 : ℚ := (-77837072210986216933793758793229428875808309535778325 / 1573489200291383354311042183023168206037068374081536)

/-- Stored center of the certified ball for `exp (ampArg2657P035)`. -/
def ampValue2657P035 : ℚ := (701454735277557633220496829692359387160168717020549310331298048804502303709 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P035)`. -/
def ampRadius2657P035 : ℚ := (27864353683646457373626805 / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P035 :
    compactExp2620 (ampArg2657P035 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P035, 0), ampRadius2657P035) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P035 :
    |Real.exp ((ampArg2657P035 : ℝ)) - (ampValue2657P035 : ℝ)|
      ≤ (ampRadius2657P035 : ℝ) := by
  have harg : ampArg2657P035 = (-77837072210986216933793758793229428875808309535778325 / 1573489200291383354311042183023168206037068374081536) := rfl
  have hsmall : |((ampArg2657P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P035 20 hsmall
  rw [ampChain2657P035] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
