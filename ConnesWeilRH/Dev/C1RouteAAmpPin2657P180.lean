import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 180 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 180 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 180. -/
def ampArg2657P180 : ℚ := (-210677430489382035732736711043775456801753938195620725 / 1965537014505398062119180639399311126059772278734848)

/-- Stored center of the certified ball for `exp (ampArg2657P180)`. -/
def ampValue2657P180 : ℚ := (60179317136913032692002134856034678882837810767521 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P180)`. -/
def ampRadius2657P180 : ℚ := (1208925819614629174706227 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P180 :
    compactExp2620 (ampArg2657P180 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P180, 0), ampRadius2657P180) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P180 :
    |Real.exp ((ampArg2657P180 : ℝ)) - (ampValue2657P180 : ℝ)|
      ≤ (ampRadius2657P180 : ℝ) := by
  have harg : ampArg2657P180 = (-210677430489382035732736711043775456801753938195620725 / 1965537014505398062119180639399311126059772278734848) := rfl
  have hsmall : |((ampArg2657P180 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P180 20 hsmall
  rw [ampChain2657P180] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 180 (vacuous-VAR budget channel). -/
def supArg2657P180 : ℚ := (-31748976329631165945620145039166037019429903457989175 / 8704521064238191417956371403054092129693277234397184)

/-- Stored center of the certified ball for `exp (supArg2657P180)`. -/
def supValue2657P180 : ℚ := (55660566292747265673443813898676136382061936542822396260835248487519002449330942145510321185627 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P180)`. -/
def supRadius2657P180 : ℚ := (35279197851499383328304024280506205798959059611 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P180 :
    compactExp2620 (supArg2657P180 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P180, 0), supRadius2657P180) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P180 :
    |Real.exp ((supArg2657P180 : ℝ)) - (supValue2657P180 : ℝ)|
      ≤ (supRadius2657P180 : ℝ) := by
  have harg : supArg2657P180 = (-31748976329631165945620145039166037019429903457989175 / 8704521064238191417956371403054092129693277234397184) := rfl
  have hsmall : |((supArg2657P180 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P180 20 hsmall
  rw [supChain2657P180] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
