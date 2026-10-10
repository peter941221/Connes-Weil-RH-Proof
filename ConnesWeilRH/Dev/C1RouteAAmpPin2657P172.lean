import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 172 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 172 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 172. -/
def ampArg2657P172 : ℚ := (-2769612795718287820505602833633394570311242913287375 / 38912481093935290197173108671071035398339203956736)

/-- Stored center of the certified ball for `exp (ampArg2657P172)`. -/
def ampValue2657P172 : ℚ := (262119689222205175423289901730640121310300105211138902342917884719 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P172)`. -/
def ampRadius2657P172 : ℚ := (2417851971527996487158305 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P172 :
    compactExp2620 (ampArg2657P172 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P172, 0), ampRadius2657P172) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P172 :
    |Real.exp ((ampArg2657P172 : ℝ)) - (ampValue2657P172 : ℝ)|
      ≤ (ampRadius2657P172 : ℝ) := by
  have harg : ampArg2657P172 = (-2769612795718287820505602833633394570311242913287375 / 38912481093935290197173108671071035398339203956736) := rfl
  have hsmall : |((ampArg2657P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P172 20 hsmall
  rw [ampChain2657P172] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 172 (vacuous-VAR budget channel). -/
def supArg2657P172 : ℚ := (-55847042093911727476988701237449445175243028530523175 / 38095318990962649103032473388978543654974080673644544)

/-- Stored center of the certified ball for `exp (supArg2657P172)`. -/
def supValue2657P172 : ℚ := (246547632039632300209609048024195023319307945383157693571892678833654457682311039308601176739757 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288)

/-- Stored radius of the certified ball for `exp (supArg2657P172)`. -/
def supRadius2657P172 : ℚ := (19533543167967755354775761182144312778289443643 / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P172 :
    compactExp2620 (supArg2657P172 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P172, 0), supRadius2657P172) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P172 :
    |Real.exp ((supArg2657P172 : ℝ)) - (supValue2657P172 : ℝ)|
      ≤ (supRadius2657P172 : ℝ) := by
  have harg : supArg2657P172 = (-55847042093911727476988701237449445175243028530523175 / 38095318990962649103032473388978543654974080673644544) := rfl
  have hsmall : |((supArg2657P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P172 20 hsmall
  rw [supChain2657P172] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
