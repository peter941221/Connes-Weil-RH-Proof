import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 182 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 182 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 182. -/
def ampArg2657P182 : ℚ := (-22570961414162062842014395894871856284353806641991 / 182687704666362864775460604089535377456991567872)

/-- Stored center of the certified ball for `exp (ampArg2657P182)`. -/
def ampValue2657P182 : ℚ := (147100385697823410318125363527749111641647 / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768)

/-- Stored radius of the certified ball for `exp (ampArg2657P182)`. -/
def ampRadius2657P182 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P182 :
    compactExp2620 (ampArg2657P182 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P182, 0), ampRadius2657P182) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P182 :
    |Real.exp ((ampArg2657P182 : ℝ)) - (ampValue2657P182 : ℝ)|
      ≤ (ampRadius2657P182 : ℝ) := by
  have harg : ampArg2657P182 = (-22570961414162062842014395894871856284353806641991 / 182687704666362864775460604089535377456991567872) := rfl
  have hsmall : |((ampArg2657P182 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P182 20 hsmall
  rw [ampChain2657P182] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 182 (vacuous-VAR budget channel). -/
def supArg2657P182 : ℚ := (-42530556921601927266517813430416034979698127681223 / 8586322119319054644446648392208162740478603689984)

/-- Stored center of the certified ball for `exp (supArg2657P182)`. -/
def supValue2657P182 : ℚ := (15080349918888634170222791304456459458520023319985345049284818006639829256988725646612545159227 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P182)`. -/
def supRadius2657P182 : ℚ := (9558352465061747683389637391180456257018367321 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P182 :
    compactExp2620 (supArg2657P182 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P182, 0), supRadius2657P182) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P182 :
    |Real.exp ((supArg2657P182 : ℝ)) - (supValue2657P182 : ℝ)|
      ≤ (supRadius2657P182 : ℝ) := by
  have harg : supArg2657P182 = (-42530556921601927266517813430416034979698127681223 / 8586322119319054644446648392208162740478603689984) := rfl
  have hsmall : |((supArg2657P182 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P182 20 hsmall
  rw [supChain2657P182] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
