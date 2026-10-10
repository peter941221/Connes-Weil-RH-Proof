import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 135 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 135. -/
def ampArg2657P135 : ℚ := (-206641051679999629351547010287689853375321391627519975 / 6108894156338507835226627140149973486784341038071808)

/-- Stored center of the certified ball for `exp (ampArg2657P135)`. -/
def ampValue2657P135 : ℚ := (4355518533321954872826413216407261231348320050815095558891819750160578966854362797 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P135)`. -/
def ampRadius2657P135 : ℚ := (345090862531355731116684983803647 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P135 :
    compactExp2620 (ampArg2657P135 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P135, 0), ampRadius2657P135) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P135 :
    |Real.exp ((ampArg2657P135 : ℝ)) - (ampValue2657P135 : ℝ)|
      ≤ (ampRadius2657P135 : ℝ) := by
  have harg : ampArg2657P135 = (-206641051679999629351547010287689853375321391627519975 / 6108894156338507835226627140149973486784341038071808) := rfl
  have hsmall : |((ampArg2657P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P135 20 hsmall
  rw [ampChain2657P135] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
