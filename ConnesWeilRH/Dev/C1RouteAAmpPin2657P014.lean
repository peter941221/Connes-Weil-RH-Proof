import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 014 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 014 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 014. -/
def ampArg2657P014 : ℚ := (-76585537851606201122328590277431457793252695507628675 / 857353397999240924391236614992189526405661428023296)

/-- Stored center of the certified ball for `exp (ampArg2657P014)`. -/
def ampValue2657P014 : ℚ := (3427718940307764118921139144518547065727054778058364854301 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P014)`. -/
def ampRadius2657P014 : ℚ := (2417851639229262695126217 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P014 :
    compactExp2620 (ampArg2657P014 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P014, 0), ampRadius2657P014) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P014 :
    |Real.exp ((ampArg2657P014 : ℝ)) - (ampValue2657P014 : ℝ)|
      ≤ (ampRadius2657P014 : ℝ) := by
  have harg : ampArg2657P014 = (-76585537851606201122328590277431457793252695507628675 / 857353397999240924391236614992189526405661428023296) := rfl
  have hsmall : |((ampArg2657P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P014 20 hsmall
  rw [ampChain2657P014] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 014 (vacuous-VAR budget channel). -/
def supArg2657P014 : ℚ := (-306622560458928354631338138106665219113577911513157825 / 155180965037862607314813827313586304279424718472216576)

/-- Stored center of the certified ball for `exp (supArg2657P014)`. -/
def supValue2657P014 : ℚ := (148062396368317637347831624520048086194379876210390508135294223035176567430109977842703326640579 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P014)`. -/
def supRadius2657P014 : ℚ := (375383478615042844341237380036880337610738123857 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P014 :
    compactExp2620 (supArg2657P014 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P014, 0), supRadius2657P014) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P014 :
    |Real.exp ((supArg2657P014 : ℝ)) - (supValue2657P014 : ℝ)|
      ≤ (supRadius2657P014 : ℝ) := by
  have harg : supArg2657P014 = (-306622560458928354631338138106665219113577911513157825 / 155180965037862607314813827313586304279424718472216576) := rfl
  have hsmall : |((supArg2657P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P014 20 hsmall
  rw [supChain2657P014] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
