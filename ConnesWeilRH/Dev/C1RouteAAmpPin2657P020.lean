import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 020 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 020 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 020. -/
def ampArg2657P020 : ℚ := (-77182299525918520614513552838195134308906668378921575 / 1083886151785530876712807764063213394452330972184576)

/-- Stored center of the certified ball for `exp (ampArg2657P020)`. -/
def ampValue2657P020 : ℚ := (253502785240012108840018621612613941142348543104763246687544814105 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P020)`. -/
def ampRadius2657P020 : ℚ := (302231495075505215619203 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P020 :
    compactExp2620 (ampArg2657P020 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P020, 0), ampRadius2657P020) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P020 :
    |Real.exp ((ampArg2657P020 : ℝ)) - (ampValue2657P020 : ℝ)|
      ≤ (ampRadius2657P020 : ℝ) := by
  have harg : ampArg2657P020 = (-77182299525918520614513552838195134308906668378921575 / 1083886151785530876712807764063213394452330972184576) := rfl
  have hsmall : |((ampArg2657P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P020 20 hsmall
  rw [ampChain2657P020] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 020 (vacuous-VAR budget channel). -/
def supArg2657P020 : ℚ := (-8546823256905822115755315981410708811349387421688755 / 7587203062498716136989654348442493761166316805292032)

/-- Stored center of the certified ball for `exp (supArg2657P020)`. -/
def supValue2657P020 : ℚ := (346214376756284796223933591294687085663608883054891338487964062036326327081009585182543923356601 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P020)`. -/
def supRadius2657P020 : ℚ := (219439666993938351378200216697496441496333310153 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P020 :
    compactExp2620 (supArg2657P020 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P020, 0), supRadius2657P020) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P020 :
    |Real.exp ((supArg2657P020 : ℝ)) - (supValue2657P020 : ℝ)|
      ≤ (supRadius2657P020 : ℝ) := by
  have harg : supArg2657P020 = (-8546823256905822115755315981410708811349387421688755 / 7587203062498716136989654348442493761166316805292032) := rfl
  have hsmall : |((supArg2657P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P020 20 hsmall
  rw [supChain2657P020] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
