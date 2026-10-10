import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 178 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 178 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 178. -/
def ampArg2657P178 : ℚ := (-69942789281245674989613674896588537722176592142140475 / 737510263738106885098534458709454318793874959499264)

/-- Stored center of the certified ball for `exp (ampArg2657P178)`. -/
def ampValue2657P178 : ℚ := (13889625678793836370267737222422132425128194433251074401 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P178)`. -/
def ampRadius2657P178 : ℚ := (2417851639229258367033469 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P178 :
    compactExp2620 (ampArg2657P178 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P178, 0), ampRadius2657P178) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P178 :
    |Real.exp ((ampArg2657P178 : ℝ)) - (ampValue2657P178 : ℝ)|
      ≤ (ampRadius2657P178 : ℝ) := by
  have harg : ampArg2657P178 = (-69942789281245674989613674896588537722176592142140475 / 737510263738106885098534458709454318793874959499264) := rfl
  have hsmall : |((ampArg2657P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P178 20 hsmall
  rw [ampChain2657P178] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 178 (vacuous-VAR budget channel). -/
def supArg2657P178 : ℚ := (-47381404116057513313817112701095876859275540016855275 / 16962736065976458357266292550317449332259124068483072)

/-- Stored center of the certified ball for `exp (supArg2657P178)`. -/
def supValue2657P178 : ℚ := (16345920345986246234048065891509010778970454530644976201865878806184295857791058542139782915303 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (supArg2657P178)`. -/
def supRadius2657P178 : ℚ := (165767767485239260192768497626299942893754012969 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P178 :
    compactExp2620 (supArg2657P178 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P178, 0), supRadius2657P178) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P178 :
    |Real.exp ((supArg2657P178 : ℝ)) - (supValue2657P178 : ℝ)|
      ≤ (supRadius2657P178 : ℝ) := by
  have harg : supArg2657P178 = (-47381404116057513313817112701095876859275540016855275 / 16962736065976458357266292550317449332259124068483072) := rfl
  have hsmall : |((supArg2657P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P178 20 hsmall
  rw [supChain2657P178] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
