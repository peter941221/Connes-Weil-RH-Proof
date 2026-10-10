import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 177 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 177 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 177. -/
def ampArg2657P177 : ℚ := (-8377275211472234970656079300003675933813606510673875 / 93353417084511423900260368689752577880522691182592)

/-- Stored center of the certified ball for `exp (ampArg2657P177)`. -/
def ampValue2657P177 : ℚ := (569067012674821829204679536765956007156499257594508042633 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P177)`. -/
def ampRadius2657P177 : ℚ := (1208925819614630617664863 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P177 :
    compactExp2620 (ampArg2657P177 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P177, 0), ampRadius2657P177) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P177 :
    |Real.exp ((ampArg2657P177 : ℝ)) - (ampValue2657P177 : ℝ)|
      ≤ (ampRadius2657P177 : ℝ) := by
  have harg : ampArg2657P177 = (-8377275211472234970656079300003675933813606510673875 / 93353417084511423900260368689752577880522691182592) := rfl
  have hsmall : |((ampArg2657P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P177 20 hsmall
  rw [ampChain2657P177] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 177 (vacuous-VAR budget channel). -/
def supArg2657P177 : ℚ := (-239416528292348249371843338026321197298908336887813675 / 96807493516638346584570002331273423262102030756347904)

/-- Stored center of the certified ball for `exp (supArg2657P177)`. -/
def supValue2657P177 : ℚ := (22513672614572695316757031476190579100938400691795078734591058888619287799141126237890981656361 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072)

/-- Stored radius of the certified ball for `exp (supArg2657P177)`. -/
def supRadius2657P177 : ℚ := (14269768957538159682307431169700221113781077147 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P177 :
    compactExp2620 (supArg2657P177 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P177, 0), supRadius2657P177) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P177 :
    |Real.exp ((supArg2657P177 : ℝ)) - (supValue2657P177 : ℝ)|
      ≤ (supRadius2657P177 : ℝ) := by
  have harg : supArg2657P177 = (-239416528292348249371843338026321197298908336887813675 / 96807493516638346584570002331273423262102030756347904) := rfl
  have hsmall : |((supArg2657P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P177 20 hsmall
  rw [supChain2657P177] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
