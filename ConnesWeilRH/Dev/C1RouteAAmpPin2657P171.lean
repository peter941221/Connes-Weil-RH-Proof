import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 171 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 171 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 171. -/
def ampArg2657P171 : ℚ := (-207431517908245407971975997163200495115436183509042575 / 3030971708119626289489666882449481447388947102564352)

/-- Stored center of the certified ball for `exp (ampArg2657P171)`. -/
def ampValue2657P171 : ℚ := (2025942810355250688409887004176825351554475844141193280542243180017 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P171)`. -/
def ampRadius2657P171 : ℚ := (2417856775939750360972789 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P171 :
    compactExp2620 (ampArg2657P171 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P171, 0), ampRadius2657P171) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P171 :
    |Real.exp ((ampArg2657P171 : ℝ)) - (ampValue2657P171 : ℝ)|
      ≤ (ampRadius2657P171 : ℝ) := by
  have harg : ampArg2657P171 = (-207431517908245407971975997163200495115436183509042575 / 3030971708119626289489666882449481447388947102564352) := rfl
  have hsmall : |((ampArg2657P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P171 20 hsmall
  rw [ampChain2657P171] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 171 (vacuous-VAR budget channel). -/
def supArg2657P171 : ℚ := (-5503910647785338181401486169411897285450437420592007675 / 4113028607918332874837477959483946324106801218179825664)

/-- Stored center of the certified ball for `exp (supArg2657P171)`. -/
def supValue2657P171 : ℚ := (560326247351887619779134668786041798805026744472284991317346408588347276497263077763938515383829 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P171)`. -/
def supRadius2657P171 : ℚ := (177574702560802767477608392191480694752678184001 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P171 :
    compactExp2620 (supArg2657P171 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P171, 0), supRadius2657P171) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P171 :
    |Real.exp ((supArg2657P171 : ℝ)) - (supValue2657P171 : ℝ)|
      ≤ (supRadius2657P171 : ℝ) := by
  have harg : supArg2657P171 = (-5503910647785338181401486169411897285450437420592007675 / 4113028607918332874837477959483946324106801218179825664) := rfl
  have hsmall : |((supArg2657P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P171 20 hsmall
  rw [supChain2657P171] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
