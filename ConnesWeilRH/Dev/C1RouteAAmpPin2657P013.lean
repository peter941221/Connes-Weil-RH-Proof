import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 013 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 013 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 013. -/
def ampArg2657P013 : ℚ := (-76465566658291661603727487047665648140896673525422225 / 817892853791306545599737124508849884874951249362944)

/-- Stored center of the certified ball for `exp (ampArg2657P013)`. -/
def ampValue2657P013 : ℚ := (3333358066558021712824439772139519452503375493373905387 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536)

/-- Stored radius of the certified ball for `exp (ampArg2657P013)`. -/
def ampRadius2657P013 : ℚ := (1208925819614629208525539 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P013 :
    compactExp2620 (ampArg2657P013 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P013, 0), ampRadius2657P013) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P013 :
    |Real.exp ((ampArg2657P013 : ℝ)) - (ampValue2657P013 : ℝ)|
      ≤ (ampRadius2657P013 : ℝ) := by
  have harg : ampArg2657P013 = (-76465566658291661603727487047665648140896673525422225 / 817892853791306545599737124508849884874951249362944) := rfl
  have hsmall : |((ampArg2657P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P013 20 hsmall
  rw [ampChain2657P013] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 013 (vacuous-VAR budget channel). -/
def supArg2657P013 : ℚ := (-492145453202668261823944219779349187471152865022869525 / 223284749085026686948728234990916018570861691076083712)

/-- Stored center of the certified ball for `exp (supArg2657P013)`. -/
def supValue2657P013 : ℚ := (235701997966899977923198057086862938210148610912851103961898251360013851152339644526222051176823 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P013)`. -/
def supRadius2657P013 : ℚ := (149394203626448194226755038325051075016448642593 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P013 :
    compactExp2620 (supArg2657P013 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P013, 0), supRadius2657P013) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P013 :
    |Real.exp ((supArg2657P013 : ℝ)) - (supValue2657P013 : ℝ)|
      ≤ (supRadius2657P013 : ℝ) := by
  have harg : supArg2657P013 = (-492145453202668261823944219779349187471152865022869525 / 223284749085026686948728234990916018570861691076083712) := rfl
  have hsmall : |((supArg2657P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P013 20 hsmall
  rw [supChain2657P013] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
