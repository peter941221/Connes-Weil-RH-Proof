import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 004 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 004 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 004. -/
def ampArg2657P004 : ℚ := (-75104273199273249014807726993644941126683609907479175 / 440825431359933592703186437668048865803720653275136)

/-- Stored center of the certified ball for `exp (ampArg2657P004)`. -/
def ampValue2657P004 : ℚ := (2722236144454915641305 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (ampArg2657P004)`. -/
def ampRadius2657P004 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P004 :
    compactExp2620 (ampArg2657P004 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P004, 0), ampRadius2657P004) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P004 :
    |Real.exp ((ampArg2657P004 : ℝ)) - (ampValue2657P004 : ℝ)|
      ≤ (ampRadius2657P004 : ℝ) := by
  have harg : ampArg2657P004 = (-75104273199273249014807726993644941126683609907479175 / 440825431359933592703186437668048865803720653275136) := rfl
  have hsmall : |((ampArg2657P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P004 20 hsmall
  rw [ampChain2657P004] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 004 (vacuous-VAR budget channel). -/
def supArg2657P004 : ℚ := (-2204097322409658050087221060256654074122154650142232225 / 252592972169241948618925828783792000105531934326652928)

/-- Stored center of the certified ball for `exp (supArg2657P004)`. -/
def supValue2657P004 : ℚ := (86683163361037208790327256534846403890744648828023386280096414587927186425991692504346139429 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (supArg2657P004)`. -/
def supRadius2657P004 : ℚ := (109884878484299462383585904259848295734092731 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P004 :
    compactExp2620 (supArg2657P004 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P004, 0), supRadius2657P004) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P004 :
    |Real.exp ((supArg2657P004 : ℝ)) - (supValue2657P004 : ℝ)|
      ≤ (supRadius2657P004 : ℝ) := by
  have harg : supArg2657P004 = (-2204097322409658050087221060256654074122154650142232225 / 252592972169241948618925828783792000105531934326652928) := rfl
  have hsmall : |((supArg2657P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P004 20 hsmall
  rw [supChain2657P004] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
