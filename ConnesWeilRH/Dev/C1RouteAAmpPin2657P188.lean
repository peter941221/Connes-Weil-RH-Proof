import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 188 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 188 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 188. -/
def ampArg2657P188 : ℚ := (-71618074421256389094531411810419985497195351585405975 / 306367280725490524228447433058150827995374859321344)

/-- Stored center of the certified ball for `exp (ampArg2657P188)`. -/
def ampValue2657P188 : ℚ := (0 / 1)

/-- Stored radius of the certified ball for `exp (ampArg2657P188)`. -/
def ampRadius2657P188 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P188 :
    compactExp2620 (ampArg2657P188 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P188, 0), ampRadius2657P188) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P188 :
    |Real.exp ((ampArg2657P188 : ℝ)) - (ampValue2657P188 : ℝ)|
      ≤ (ampRadius2657P188 : ℝ) := by
  have harg : ampArg2657P188 = (-71618074421256389094531411810419985497195351585405975 / 306367280725490524228447433058150827995374859321344) := rfl
  have hsmall : |((ampArg2657P188 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P188 20 hsmall
  rw [ampChain2657P188] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 188 (vacuous-VAR budget channel). -/
def supArg2657P188 : ℚ := (-570143303166913313861184310276786107750407078853212725 / 29717626230372580850159401006640630315551361354170368)

/-- Stored center of the certified ball for `exp (supArg2657P188)`. -/
def supValue2657P188 : ℚ := (9942679179792782165718756122447100646594672190776235744104582871680651534583843333107631 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P188)`. -/
def supRadius2657P188 : ℚ := (12604073839518744513674750262147696153007 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P188 :
    compactExp2620 (supArg2657P188 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P188, 0), supRadius2657P188) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P188 :
    |Real.exp ((supArg2657P188 : ℝ)) - (supValue2657P188 : ℝ)|
      ≤ (supRadius2657P188 : ℝ) := by
  have harg : supArg2657P188 = (-570143303166913313861184310276786107750407078853212725 / 29717626230372580850159401006640630315551361354170368) := rfl
  have hsmall : |((supArg2657P188 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P188 20 hsmall
  rw [supChain2657P188] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
