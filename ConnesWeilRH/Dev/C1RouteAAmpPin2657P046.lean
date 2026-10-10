import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 046 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 046. -/
def ampArg2657P046 : ℚ := (-77670565835569654805855321121927938428858610991966275 / 1862866524482902132115371779900992243928943017590784)

/-- Stored center of the certified ball for `exp (ampArg2657P046)`. -/
def ampValue2657P046 : ℚ := (416884527201773946195306964858934598283344965478717773216438493472705094570181 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P046)`. -/
def ampRadius2657P046 : ℚ := (2113942156461837092454790605235 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P046 :
    compactExp2620 (ampArg2657P046 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P046, 0), ampRadius2657P046) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P046 :
    |Real.exp ((ampArg2657P046 : ℝ)) - (ampValue2657P046 : ℝ)|
      ≤ (ampRadius2657P046 : ℝ) := by
  have harg : ampArg2657P046 = (-77670565835569654805855321121927938428858610991966275 / 1862866524482902132115371779900992243928943017590784) := rfl
  have hsmall : |((ampArg2657P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P046 20 hsmall
  rw [ampChain2657P046] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
