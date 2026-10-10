import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 167 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 167 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 167. -/
def ampArg2657P167 : ℚ := (-2752561665694882970638588316816706419736283550159125 / 46219989280589804788191532834652450496618866671616)

/-- Stored center of the certified ball for `exp (ampArg2657P167)`. -/
def ampValue2657P167 : ℚ := (29231194482124640903616401356085544372583704451067352232168945679386997 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P167)`. -/
def ampRadius2657P167 : ℚ := (1227454342521029303857897 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P167 :
    compactExp2620 (ampArg2657P167 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P167, 0), ampRadius2657P167) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P167 :
    |Real.exp ((ampArg2657P167 : ℝ)) - (ampValue2657P167 : ℝ)|
      ≤ (ampRadius2657P167 : ℝ) := by
  have harg : ampArg2657P167 = (-2752561665694882970638588316816706419736283550159125 / 46219989280589804788191532834652450496618866671616) := rfl
  have hsmall : |((ampArg2657P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P167 20 hsmall
  rw [ampChain2657P167] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 167 (vacuous-VAR budget channel). -/
def supArg2657P167 : ℚ := (-69052639168055695657002903629533564883111483843098025 / 71964523309878326055214216623553865423235575407706112)

/-- Stored center of the certified ball for `exp (supArg2657P167)`. -/
def supValue2657P167 : ℚ := (409116404354868420101719687693870758349496695385833829755603541995332933809464016025861592543947 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P167)`. -/
def supRadius2657P167 : ℚ := (1037234260245453684338286666753162805040947402661 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P167 :
    compactExp2620 (supArg2657P167 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P167, 0), supRadius2657P167) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P167 :
    |Real.exp ((supArg2657P167 : ℝ)) - (supValue2657P167 : ℝ)|
      ≤ (supRadius2657P167 : ℝ) := by
  have harg : supArg2657P167 = (-69052639168055695657002903629533564883111483843098025 / 71964523309878326055214216623553865423235575407706112) := rfl
  have hsmall : |((supArg2657P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P167 20 hsmall
  rw [supChain2657P167] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
