import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 000 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 000 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 000. -/
def ampArg2657P000 : ℚ := (-222982678143220785860743601528607854774721614607727725 / 781720688267366698374195924899121880138466918924288)

/-- Stored center of the certified ball for `exp (ampArg2657P000)`. -/
def ampValue2657P000 : ℚ := (0 / 1)

/-- Stored radius of the certified ball for `exp (ampArg2657P000)`. -/
def ampRadius2657P000 : ℚ := (2417851639229258349412353 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P000 :
    compactExp2620 (ampArg2657P000 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P000, 0), ampRadius2657P000) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P000 :
    |Real.exp ((ampArg2657P000 : ℝ)) - (ampValue2657P000 : ℝ)|
      ≤ (ampRadius2657P000 : ℝ) := by
  have harg : ampArg2657P000 = (-222982678143220785860743601528607854774721614607727725 / 781720688267366698374195924899121880138466918924288) := rfl
  have hsmall : |((ampArg2657P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P000 20 hsmall
  rw [ampChain2657P000] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 000 (vacuous-VAR budget channel). -/
def supArg2657P000 : ℚ := (-276696112533112930905987263122089334744681161173860675 / 10162368947475767078864547023688584441800069946015744)

/-- Stored center of the certified ball for `exp (supArg2657P000)`. -/
def supValue2657P000 : ℚ := (3197691377341402564338450202666688600042447202216052245633796210391688220887987423165 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P000)`. -/
def supRadius2657P000 : ℚ := (1013415162644801888406605656858355059 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P000 :
    compactExp2620 (supArg2657P000 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P000, 0), supRadius2657P000) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P000 :
    |Real.exp ((supArg2657P000 : ℝ)) - (supValue2657P000 : ℝ)|
      ≤ (supRadius2657P000 : ℝ) := by
  have harg : supArg2657P000 = (-276696112533112930905987263122089334744681161173860675 / 10162368947475767078864547023688584441800069946015744) := rfl
  have hsmall : |((supArg2657P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P000 20 hsmall
  rw [supChain2657P000] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
