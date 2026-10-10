import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 005 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 005 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 005. -/
def ampArg2657P005 : ℚ := (-75281446984644508018848253310889514950668759867569825 / 484670480479860680249296982649537356393398629564416)

/-- Stored center of the certified ball for `exp (ampArg2657P005)`. -/
def ampValue2657P005 : ℚ := (37305605181357415668294592019 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P005)`. -/
def ampRadius2657P005 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P005 :
    compactExp2620 (ampArg2657P005 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P005, 0), ampRadius2657P005) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P005 :
    |Real.exp ((ampArg2657P005 : ℝ)) - (ampValue2657P005 : ℝ)|
      ≤ (ampRadius2657P005 : ℝ) := by
  have harg : ampArg2657P005 = (-75281446984644508018848253310889514950668759867569825 / 484670480479860680249296982649537356393398629564416) := rfl
  have hsmall : |((ampArg2657P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P005 20 hsmall
  rw [ampChain2657P005] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 005 (vacuous-VAR budget channel). -/
def supArg2657P005 : ℚ := (-65350690795090816610453953394252519415498126376346175 / 9208739129117352924736642670341209771474573961723904)

/-- Stored center of the certified ball for `exp (supArg2657P005)`. -/
def supValue2657P005 : ℚ := (884212454155935168859919872465234856497314026649983174591462838241007655092130507225278082473 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P005)`. -/
def supRadius2657P005 : ℚ := (280220008537848098071799215250748671516700833 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P005 :
    compactExp2620 (supArg2657P005 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P005, 0), supRadius2657P005) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P005 :
    |Real.exp ((supArg2657P005 : ℝ)) - (supValue2657P005 : ℝ)|
      ≤ (supRadius2657P005 : ℝ) := by
  have harg : supArg2657P005 = (-65350690795090816610453953394252519415498126376346175 / 9208739129117352924736642670341209771474573961723904) := rfl
  have hsmall : |((supArg2657P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P005 20 hsmall
  rw [supChain2657P005] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
