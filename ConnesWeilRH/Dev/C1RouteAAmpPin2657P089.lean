import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 089 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 089. -/
def ampArg2657P089 : ℚ := (-73754446276739240559259027383085701784301336400762425 / 2428467658129961561460197810162193772535788911722496)

/-- Stored center of the certified ball for `exp (ampArg2657P089)`. -/
def ampValue2657P089 : ℚ := (34488822769724135077450053700119102027225465650010658580304619983152165622968722237 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P089)`. -/
def ampRadius2657P089 : ℚ := (10930260799068792254378433517716101 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P089 :
    compactExp2620 (ampArg2657P089 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P089, 0), ampRadius2657P089) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P089 :
    |Real.exp ((ampArg2657P089 : ℝ)) - (ampValue2657P089 : ℝ)|
      ≤ (ampRadius2657P089 : ℝ) := by
  have harg : ampArg2657P089 = (-73754446276739240559259027383085701784301336400762425 / 2428467658129961561460197810162193772535788911722496) := rfl
  have hsmall : |((ampArg2657P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P089 20 hsmall
  rw [ampChain2657P089] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
