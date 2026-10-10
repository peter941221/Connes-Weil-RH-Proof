import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 110 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 110. -/
def ampArg2657P110 : ℚ := (-71200837451059699956259648413088687765796536695387075 / 2377315100823379959323068841017123866847831272718336)

/-- Stored center of the certified ball for `exp (ampArg2657P110)`. -/
def ampValue2657P110 : ℚ := (52525861514763194834086291681460303167233931856581149336848079996252304295312313649 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144)

/-- Stored radius of the certified ball for `exp (ampArg2657P110)`. -/
def ampRadius2657P110 : ℚ := (66586341732254263771095440728849701 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P110 :
    compactExp2620 (ampArg2657P110 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P110, 0), ampRadius2657P110) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P110 :
    |Real.exp ((ampArg2657P110 : ℝ)) - (ampValue2657P110 : ℝ)|
      ≤ (ampRadius2657P110 : ℝ) := by
  have harg : ampArg2657P110 = (-71200837451059699956259648413088687765796536695387075 / 2377315100823379959323068841017123866847831272718336) := rfl
  have hsmall : |((ampArg2657P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P110 20 hsmall
  rw [ampChain2657P110] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
