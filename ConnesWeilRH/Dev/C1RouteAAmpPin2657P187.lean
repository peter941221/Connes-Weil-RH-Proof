import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 187 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 187 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 187. -/
def ampArg2657P187 : ℚ := (-2856819801314829791078862365145448136058378402638125 / 14066953259309940587710466514894224064188350726144)

/-- Stored center of the certified ball for `exp (ampArg2657P187)`. -/
def ampValue2657P187 : ℚ := (134864399 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P187)`. -/
def ampRadius2657P187 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P187 :
    compactExp2620 (ampArg2657P187 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P187, 0), ampRadius2657P187) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P187 :
    |Real.exp ((ampArg2657P187 : ℝ)) - (ampValue2657P187 : ℝ)|
      ≤ (ampRadius2657P187 : ℝ) := by
  have harg : ampArg2657P187 = (-2856819801314829791078862365145448136058378402638125 / 14066953259309940587710466514894224064188350726144) := rfl
  have hsmall : |((ampArg2657P187 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P187 20 hsmall
  rw [ampChain2657P187] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 187 (vacuous-VAR budget channel). -/
def supArg2657P187 : ℚ := (-38660747927885325295919799910465749992082628984109525 / 2714921979046818533428120037374585244388351690145792)

/-- Stored center of the certified ball for `exp (supArg2657P187)`. -/
def supValue2657P187 : ℚ := (698511840058452456198481545823008437378776972950136836158896671979103460809482701807727957 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P187)`. -/
def supRadius2657P187 : ℚ := (885480978432559942961822645760332772125841 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P187 :
    compactExp2620 (supArg2657P187 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P187, 0), supRadius2657P187) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P187 :
    |Real.exp ((supArg2657P187 : ℝ)) - (supValue2657P187 : ℝ)|
      ≤ (supRadius2657P187 : ℝ) := by
  have harg : supArg2657P187 = (-38660747927885325295919799910465749992082628984109525 / 2714921979046818533428120037374585244388351690145792) := rfl
  have hsmall : |((supArg2657P187 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P187 20 hsmall
  rw [supChain2657P187] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
