import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 021 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 021 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 021. -/
def ampArg2657P021 : ℚ := (-231785828117969081682576377463308837485703073313395075 / 3359809576519079446085495969810645126811531924733952)

/-- Stored center of the certified ball for `exp (ampArg2657P021)`. -/
def ampValue2657P021 : ℚ := (1168297142526914603497094092586843819637376079756326653759356423831 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P021)`. -/
def ampRadius2657P021 : ℚ := (604463650352323082489309 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P021 :
    compactExp2620 (ampArg2657P021 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P021, 0), ampRadius2657P021) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P021 :
    |Real.exp ((ampArg2657P021 : ℝ)) - (ampValue2657P021 : ℝ)|
      ≤ (ampRadius2657P021 : ℝ) := by
  have harg : ampArg2657P021 = (-231785828117969081682576377463308837485703073313395075 / 3359809576519079446085495969810645126811531924733952) := rfl
  have hsmall : |((ampArg2657P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P021 20 hsmall
  rw [ampChain2657P021] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 021 (vacuous-VAR budget channel). -/
def supArg2657P021 : ℚ := (-1315108627292577258535940887040856558605400749560373175 / 1266648210347692951174231980618613212807947535624699904)

/-- Stored center of the certified ball for `exp (supArg2657P021)`. -/
def supValue2657P021 : ℚ := (756290339471360306483682121815903228460489003608838871738356879503561492468519510004036231974191 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P021)`. -/
def supRadius2657P021 : ℚ := (958712852057032191109923328797520718096162579083 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P021 :
    compactExp2620 (supArg2657P021 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P021, 0), supRadius2657P021) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P021 :
    |Real.exp ((supArg2657P021 : ℝ)) - (supValue2657P021 : ℝ)|
      ≤ (supRadius2657P021 : ℝ) := by
  have harg : supArg2657P021 = (-1315108627292577258535940887040856558605400749560373175 / 1266648210347692951174231980618613212807947535624699904) := rfl
  have hsmall : |((supArg2657P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P021 20 hsmall
  rw [supChain2657P021] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
