import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 008 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 008 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 008. -/
def ampArg2657P008 : ℚ := (-75773346532355125205447788720548926736492533058806975 / 613282624564980137051221247928570262123120693346304)

/-- Stored center of the certified ball for `exp (ampArg2657P008)`. -/
def ampValue2657P008 : ℚ := (2343538154884838737340107663839723750809401 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (ampArg2657P008)`. -/
def ampRadius2657P008 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P008 :
    compactExp2620 (ampArg2657P008 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P008, 0), ampRadius2657P008) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P008 :
    |Real.exp ((ampArg2657P008 : ℝ)) - (ampValue2657P008 : ℝ)|
      ≤ (ampRadius2657P008 : ℝ) := by
  have harg : ampArg2657P008 = (-75773346532355125205447788720548926736492533058806975 / 613282624564980137051221247928570262123120693346304) := rfl
  have hsmall : |((ampArg2657P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P008 20 hsmall
  rw [ampChain2657P008] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 008 (vacuous-VAR budget channel). -/
def supArg2657P008 : ℚ := (-6301347274451207247784866297380922454074169559683099675 / 1490890060317466713171518853714354307221306405524865024)

/-- Stored center of the certified ball for `exp (supArg2657P008)`. -/
def supValue2657P008 : ℚ := (7797649983547550764970551723934852839903226403662868869815819025337869014841343276005597463413 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (supArg2657P008)`. -/
def supRadius2657P008 : ℚ := (9884735525016384225091303179076632846506145621 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P008 :
    compactExp2620 (supArg2657P008 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P008, 0), supRadius2657P008) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P008 :
    |Real.exp ((supArg2657P008 : ℝ)) - (supValue2657P008 : ℝ)|
      ≤ (supRadius2657P008 : ℝ) := by
  have harg : supArg2657P008 = (-6301347274451207247784866297380922454074169559683099675 / 1490890060317466713171518853714354307221306405524865024) := rfl
  have hsmall : |((supArg2657P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P008 20 hsmall
  rw [supChain2657P008] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
