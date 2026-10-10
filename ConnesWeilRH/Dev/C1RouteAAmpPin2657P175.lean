import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 175 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 175 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 175. -/
def ampArg2657P175 : ℚ := (-69564625881484090698039892994196844172340558789971325 / 857353397999240924391236614992189526405661428023296)

/-- Stored center of the certified ball for `exp (ampArg2657P175)`. -/
def ampValue2657P175 : ℚ := (12344272730395263321890764979344038446147219488733844699280863 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P175)`. -/
def ampRadius2657P175 : ℚ := (2417851639244907796679739 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P175 :
    compactExp2620 (ampArg2657P175 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P175, 0), ampRadius2657P175) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P175 :
    |Real.exp ((ampArg2657P175 : ℝ)) - (ampValue2657P175 : ℝ)|
      ≤ (ampRadius2657P175 : ℝ) := by
  have harg : ampArg2657P175 = (-69564625881484090698039892994196844172340558789971325 / 857353397999240924391236614992189526405661428023296) := rfl
  have hsmall : |((ampArg2657P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P175 20 hsmall
  rw [ampChain2657P175] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 175 (vacuous-VAR budget channel). -/
def supArg2657P175 : ℚ := (-306622560458928354631338138106665219113577911513157825 / 155180965037862607314813827313586304279424718472216576)

/-- Stored center of the certified ball for `exp (supArg2657P175)`. -/
def supValue2657P175 : ℚ := (148062396368317637347831624520048086194379876210390508135294223035176567430109977842703326640579 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P175)`. -/
def supRadius2657P175 : ℚ := (375383478615042844341237380036880337610738123857 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P175 :
    compactExp2620 (supArg2657P175 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P175, 0), supRadius2657P175) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P175 :
    |Real.exp ((supArg2657P175 : ℝ)) - (supValue2657P175 : ℝ)|
      ≤ (supRadius2657P175 : ℝ) := by
  have harg : supArg2657P175 = (-306622560458928354631338138106665219113577911513157825 / 155180965037862607314813827313586304279424718472216576) := rfl
  have hsmall : |((supArg2657P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P175 20 hsmall
  rw [supChain2657P175] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
