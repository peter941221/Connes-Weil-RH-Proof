import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 012 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 012 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 012. -/
def ampArg2657P012 : ℚ := (-9160744436498600047788138692591720302057584005038125 / 93353417084511423900260368689752577880522691182592)

/-- Stored center of the certified ball for `exp (ampArg2657P012)`. -/
def ampValue2657P012 : ℚ := (515707961928884938584796591333315170034675044866751991 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P012)`. -/
def ampRadius2657P012 : ℚ := (2417851639229258350068527 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P012 :
    compactExp2620 (ampArg2657P012 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P012, 0), ampRadius2657P012) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P012 :
    |Real.exp ((ampArg2657P012 : ℝ)) - (ampValue2657P012 : ℝ)|
      ≤ (ampRadius2657P012 : ℝ) := by
  have harg : ampArg2657P012 = (-9160744436498600047788138692591720302057584005038125 / 93353417084511423900260368689752577880522691182592) := rfl
  have hsmall : |((ampArg2657P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P012 20 hsmall
  rw [ampChain2657P012] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 012 (vacuous-VAR budget channel). -/
def supArg2657P012 : ℚ := (-239416528292348249371843338026321197298908336887813675 / 96807493516638346584570002331273423262102030756347904)

/-- Stored center of the certified ball for `exp (supArg2657P012)`. -/
def supValue2657P012 : ℚ := (22513672614572695316757031476190579100938400691795078734591058888619287799141126237890981656361 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (supArg2657P012)`. -/
def supRadius2657P012 : ℚ := (14269768957538159682307431169700221113781077147 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P012 :
    compactExp2620 (supArg2657P012 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P012, 0), supRadius2657P012) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P012 :
    |Real.exp ((supArg2657P012 : ℝ)) - (supValue2657P012 : ℝ)|
      ≤ (supRadius2657P012 : ℝ) := by
  have harg : supArg2657P012 = (-239416528292348249371843338026321197298908336887813675 / 96807493516638346584570002331273423262102030756347904) := rfl
  have hsmall : |((supArg2657P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P012 20 hsmall
  rw [supChain2657P012] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
