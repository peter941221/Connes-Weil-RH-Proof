import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 040 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 040. -/
def ampArg2657P040 : ℚ := (-77821786593063328117427961038371961841641656591720575 / 1712331855837819131540392242131215092904381965664256)

/-- Stored center of the certified ball for `exp (ampArg2657P040)`. -/
def ampValue2657P040 : ℚ := (9767690511587509858322025522637583813571901218650898067225355318360785629613 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P040)`. -/
def ampRadius2657P040 : ℚ := (49532639525162635932243677591 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P040 :
    compactExp2620 (ampArg2657P040 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P040, 0), ampRadius2657P040) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P040 :
    |Real.exp ((ampArg2657P040 : ℝ)) - (ampValue2657P040 : ℝ)|
      ≤ (ampRadius2657P040 : ℝ) := by
  have harg : ampArg2657P040 = (-77821786593063328117427961038371961841641656591720575 / 1712331855837819131540392242131215092904381965664256) := rfl
  have hsmall : |((ampArg2657P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P040 20 hsmall
  rw [ampChain2657P040] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
