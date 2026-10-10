import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 081 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 081. -/
def ampArg2657P081 : ℚ := (-224151567951958751135578128566167338439722084997914075 / 7174328849952736062597113383200143808113515861901312)

/-- Stored center of the certified ball for `exp (ampArg2657P081)`. -/
def ampValue2657P081 : ℚ := (57635925126813280607190591453393382867651925319926915821025527278002818967998379579 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P081)`. -/
def ampRadius2657P081 : ℚ := (18266098022868058429391959034468669 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P081 :
    compactExp2620 (ampArg2657P081 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P081, 0), ampRadius2657P081) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P081 :
    |Real.exp ((ampArg2657P081 : ℝ)) - (ampValue2657P081 : ℝ)|
      ≤ (ampRadius2657P081 : ℝ) := by
  have harg : ampArg2657P081 = (-224151567951958751135578128566167338439722084997914075 / 7174328849952736062597113383200143808113515861901312) := rfl
  have hsmall : |((ampArg2657P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P081 20 hsmall
  rw [ampChain2657P081] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
