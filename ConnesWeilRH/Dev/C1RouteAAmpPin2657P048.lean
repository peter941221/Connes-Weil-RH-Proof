import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 048 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 no supRe pin (non-vacuous panel)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 048. -/
def ampArg2657P048 : ℚ := (-232771569276700883692626786720782804285399756756846925 / 5727442228995142173575465398811023618654142644355072)

/-- Stored center of the certified ball for `exp (ampArg2657P048)`. -/
def ampValue2657P048 : ℚ := (149310458814109251125798164981436823513821099427617913169498379085161760827559 / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768)

/-- Stored radius of the certified ball for `exp (ampArg2657P048)`. -/
def ampRadius2657P048 : ℚ := (6056988941834714400469744806583 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P048 :
    compactExp2620 (ampArg2657P048 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P048, 0), ampRadius2657P048) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P048 :
    |Real.exp ((ampArg2657P048 : ℝ)) - (ampValue2657P048 : ℝ)|
      ≤ (ampRadius2657P048 : ℝ) := by
  have harg : ampArg2657P048 = (-232771569276700883692626786720782804285399756756846925 / 5727442228995142173575465398811023618654142644355072) := rfl
  have hsmall : |((ampArg2657P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P048 20 hsmall
  rw [ampChain2657P048] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
