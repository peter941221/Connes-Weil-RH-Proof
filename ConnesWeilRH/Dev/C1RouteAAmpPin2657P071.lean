import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 071 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 071. -/
def ampArg2657P071 : ℚ := (-75825837994754151906755017606378611402758443381592525 / 2301317015682173007576477229715877149825722780483584)

/-- Stored center of the certified ball for `exp (ampArg2657P071)`. -/
def ampValue2657P071 : ℚ := (5236584438010791600410147109144346295184026932576127597369067926314619658249401329 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P071)`. -/
def ampRadius2657P071 : ℚ := (3319183999049390578629112818639545 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P071 :
    compactExp2620 (ampArg2657P071 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P071, 0), ampRadius2657P071) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P071 :
    |Real.exp ((ampArg2657P071 : ℝ)) - (ampValue2657P071 : ℝ)|
      ≤ (ampRadius2657P071 : ℝ) := by
  have harg : ampArg2657P071 = (-75825837994754151906755017606378611402758443381592525 / 2301317015682173007576477229715877149825722780483584) := rfl
  have hsmall : |((ampArg2657P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P071 20 hsmall
  rw [ampChain2657P071] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
