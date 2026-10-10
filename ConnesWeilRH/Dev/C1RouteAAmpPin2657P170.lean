import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 170 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 170 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 170. -/
def ampArg2657P170 : ℚ := (-69053045519937194780095214943328851730975769832464075 / 1047348610852258303757715643245306318960932658610176)

/-- Stored center of the certified ball for `exp (ampArg2657P170)`. -/
def ampValue2657P170 : ℚ := (24829785434184143102038384819089628985678492898965472623744817213167 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P170)`. -/
def ampRadius2657P170 : ℚ := (2417914594172392183301353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P170 :
    compactExp2620 (ampArg2657P170 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P170, 0), ampRadius2657P170) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P170 :
    |Real.exp ((ampArg2657P170 : ℝ)) - (ampValue2657P170 : ℝ)|
      ≤ (ampRadius2657P170 : ℝ) := by
  have harg : ampArg2657P170 = (-69053045519937194780095214943328851730975769832464075 / 1047348610852258303757715643245306318960932658610176) := rfl
  have hsmall : |((ampArg2657P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P170 20 hsmall
  rw [ampChain2657P170] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 170 (vacuous-VAR budget channel). -/
def supArg2657P170 : ℚ := (-14122205671080608954774918135033687024684089044918575 / 11520834719374841341334872075698369508570259244711936)

/-- Stored center of the certified ball for `exp (supArg2657P170)`. -/
def supValue2657P170 : ℚ := (626962694799798084887120697901695819257963235453679612488318404024511389433604753481906630542599 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P170)`. -/
def supRadius2657P170 : ℚ := (794770565478822997095255623739492715758084435675 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P170 :
    compactExp2620 (supArg2657P170 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P170, 0), supRadius2657P170) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P170 :
    |Real.exp ((supArg2657P170 : ℝ)) - (supValue2657P170 : ℝ)|
      ≤ (supRadius2657P170 : ℝ) := by
  have harg : supArg2657P170 = (-14122205671080608954774918135033687024684089044918575 / 11520834719374841341334872075698369508570259244711936) := rfl
  have hsmall : |((supArg2657P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P170 20 hsmall
  rw [supChain2657P170] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
