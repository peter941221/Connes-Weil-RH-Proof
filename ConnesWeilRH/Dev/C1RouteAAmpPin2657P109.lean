import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 109 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 109. -/
def ampArg2657P109 : ℚ := (-71316366987616099137947164210136035872662187791721425 / 2384622609010034473914087265180705281946110935433216)

/-- Stored center of the certified ball for `exp (ampArg2657P109)`. -/
def ampValue2657P109 : ℚ := (219407838968143407950281678642113387387110379558705247268332490794382008067233407249 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P109)`. -/
def ampRadius2657P109 : ℚ := (69535102896018055633944725347755047 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P109 :
    compactExp2620 (ampArg2657P109 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P109, 0), ampRadius2657P109) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P109 :
    |Real.exp ((ampArg2657P109 : ℝ)) - (ampValue2657P109 : ℝ)|
      ≤ (ampRadius2657P109 : ℝ) := by
  have harg : ampArg2657P109 = (-71316366987616099137947164210136035872662187791721425 / 2384622609010034473914087265180705281946110935433216) := rfl
  have hsmall : |((ampArg2657P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P109 20 hsmall
  rw [ampChain2657P109] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
