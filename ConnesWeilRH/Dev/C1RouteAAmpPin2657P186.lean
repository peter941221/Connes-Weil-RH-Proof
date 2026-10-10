import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 186 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 186 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 186. -/
def ampArg2657P186 : ℚ := (-213689375548524488717038809927659742224678285904429825 / 1189479645082688612553023993226964842622472098414592)

/-- Stored center of the certified ball for `exp (ampArg2657P186)`. -/
def ampValue2657P186 : ℚ := (1018121473972157347 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P186)`. -/
def ampRadius2657P186 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P186 :
    compactExp2620 (ampArg2657P186 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P186, 0), ampRadius2657P186) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P186 :
    |Real.exp ((ampArg2657P186 : ℝ)) - (ampValue2657P186 : ℝ)|
      ≤ (ampRadius2657P186 : ℝ) := by
  have harg : ampArg2657P186 = (-213689375548524488717038809927659742224678285904429825 / 1189479645082688612553023993226964842622472098414592) := rfl
  have hsmall : |((ampArg2657P186 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P186 20 hsmall
  rw [ampChain2657P186] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 186 (vacuous-VAR budget channel). -/
def supArg2657P186 : ℚ := (-13064746924560182187324451829918884484378850026336775 / 1189479645082688612553023993226964842622472098414592)

/-- Stored center of the certified ball for `exp (supArg2657P186)`. -/
def supValue2657P186 : ℚ := (36265165677788497140730329706043996984672535140056185144188817071081683793553089082712220669 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P186)`. -/
def supRadius2657P186 : ℚ := (45972040582386250001430939374405345026783329 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P186 :
    compactExp2620 (supArg2657P186 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P186, 0), supRadius2657P186) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P186 :
    |Real.exp ((supArg2657P186 : ℝ)) - (supValue2657P186 : ℝ)|
      ≤ (supRadius2657P186 : ℝ) := by
  have harg : supArg2657P186 = (-13064746924560182187324451829918884484378850026336775 / 1189479645082688612553023993226964842622472098414592) := rfl
  have hsmall : |((supArg2657P186 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P186 20 hsmall
  rw [supChain2657P186] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
