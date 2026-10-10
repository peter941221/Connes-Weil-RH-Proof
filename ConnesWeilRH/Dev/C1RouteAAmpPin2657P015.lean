import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 015 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 015 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 015. -/
def ampArg2657P015 : ℚ := (-230098574664350658887397760605248564458400636671377975 / 2688980324984195006630004631593871220789458887507968)

/-- Stored center of the certified ball for `exp (ampArg2657P015)`. -/
def ampValue2657P015 : ℚ := (146761269584418243099915907917409914482538270401326032149091 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P015)`. -/
def ampRadius2657P015 : ℚ := (1208925819614722203937149 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P015 :
    compactExp2620 (ampArg2657P015 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P015, 0), ampRadius2657P015) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P015 :
    |Real.exp ((ampArg2657P015 : ℝ)) - (ampValue2657P015 : ℝ)|
      ≤ (ampRadius2657P015 : ℝ) := by
  have harg : ampArg2657P015 = (-230098574664350658887397760605248564458400636671377975 / 2688980324984195006630004631593871220789458887507968) := rfl
  have hsmall : |((ampArg2657P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P015 20 hsmall
  rw [ampChain2657P015] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 015 (vacuous-VAR budget channel). -/
def supArg2657P015 : ℚ := (-14364187294978000330808171181842217833138270835433925 / 8066940974952585019890013894781613662368376662523904)

/-- Stored center of the certified ball for `exp (supArg2657P015)`. -/
def supValue2657P015 : ℚ := (359984259082287269712191983099477696254145018491248740846102611066280569909534816558106363524329 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P015)`. -/
def supRadius2657P015 : ℚ := (228167518508155725588358446466307955334572122851 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P015 :
    compactExp2620 (supArg2657P015 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P015, 0), supRadius2657P015) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P015 :
    |Real.exp ((supArg2657P015 : ℝ)) - (supValue2657P015 : ℝ)|
      ≤ (supRadius2657P015 : ℝ) := by
  have harg : supArg2657P015 = (-14364187294978000330808171181842217833138270835433925 / 8066940974952585019890013894781613662368376662523904) := rfl
  have hsmall : |((supArg2657P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P015 20 hsmall
  rw [supChain2657P015] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
