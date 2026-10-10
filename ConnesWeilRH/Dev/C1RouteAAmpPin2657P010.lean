import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 010 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 010 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 010. -/
def ampArg2657P010 : ℚ := (-76069004764008910226193656783804176641121446963992075 / 696588217892841603388831283393398394243508848295936)

/-- Stored center of the certified ball for `exp (ampArg2657P010)`. -/
def ampValue2657P010 : ℚ := (8010534646797701211722101279334511361461444430111 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P010)`. -/
def ampRadius2657P010 : ℚ := (604462909807314587353093 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P010 :
    compactExp2620 (ampArg2657P010 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P010, 0), ampRadius2657P010) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P010 :
    |Real.exp ((ampArg2657P010 : ℝ)) - (ampValue2657P010 : ℝ)|
      ≤ (ampRadius2657P010 : ℝ) := by
  have harg : ampArg2657P010 = (-76069004764008910226193656783804176641121446963992075 / 696588217892841603388831283393398394243508848295936) := rfl
  have hsmall : |((ampArg2657P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P010 20 hsmall
  rw [ampChain2657P010] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 010 (vacuous-VAR budget channel). -/
def supArg2657P010 : ℚ := (-81919368265372587188020924643288742389506825760025025 / 25773764062035139325386757485555740587009827386949632)

/-- Stored center of the certified ball for `exp (supArg2657P010)`. -/
def supValue2657P010 : ℚ := (88968530011686612105074305091938526520671608278864013411083006349190762835288981990975804410495 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P010)`. -/
def supRadius2657P010 : ℚ := (112781352328521081938836841251405506890368185961 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P010 :
    compactExp2620 (supArg2657P010 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P010, 0), supRadius2657P010) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P010 :
    |Real.exp ((supArg2657P010 : ℝ)) - (supValue2657P010 : ℝ)|
      ≤ (supRadius2657P010 : ℝ) := by
  have harg : supArg2657P010 = (-81919368265372587188020924643288742389506825760025025 / 25773764062035139325386757485555740587009827386949632) := rfl
  have hsmall : |((supArg2657P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P010 20 hsmall
  rw [supChain2657P010] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
