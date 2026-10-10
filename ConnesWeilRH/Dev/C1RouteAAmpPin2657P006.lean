import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 006 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 006 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 006. -/
def ampArg2657P006 : ℚ := (-226355902731142519805715740964989598123724665334752825 / 1584085087162032400468018898060361257929573885018112)

/-- Stored center of the certified ball for `exp (ampArg2657P006)`. -/
def ampValue2657P006 : ℚ := (18690432090100815480394455973669449 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P006)`. -/
def ampRadius2657P006 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P006 :
    compactExp2620 (ampArg2657P006 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P006, 0), ampRadius2657P006) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P006 :
    |Real.exp ((ampArg2657P006 : ℝ)) - (ampValue2657P006 : ℝ)|
      ≤ (ampRadius2657P006 : ℝ) := by
  have harg : ampArg2657P006 = (-226355902731142519805715740964989598123724665334752825 / 1584085087162032400468018898060361257929573885018112) := rfl
  have hsmall : |((ampArg2657P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P006 20 hsmall
  rw [ampChain2657P006] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 006 (vacuous-VAR budget channel). -/
def supArg2657P006 : ℚ := (-6457495180107099734115925060275228094036720403893127075 / 1097770965403288453524337096355830351745194702317551616)

/-- Stored center of the certified ball for `exp (supArg2657P006)`. -/
def supValue2657P006 : ℚ := (744436605667864071984042994006339772514189024846441825887790384208431470539718073062466000189 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (supArg2657P006)`. -/
def supRadius2657P006 : ℚ := (7549526431761817358682115583301755809294747821 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P006 :
    compactExp2620 (supArg2657P006 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P006, 0), supRadius2657P006) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P006 :
    |Real.exp ((supArg2657P006 : ℝ)) - (supValue2657P006 : ℝ)|
      ≤ (supRadius2657P006 : ℝ) := by
  have harg : supArg2657P006 = (-6457495180107099734115925060275228094036720403893127075 / 1097770965403288453524337096355830351745194702317551616) := rfl
  have hsmall : |((supArg2657P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P006 20 hsmall
  rw [supChain2657P006] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
