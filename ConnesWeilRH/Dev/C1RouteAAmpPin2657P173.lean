import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# Real-exponential pins for panel 173 of entry (0, 3) (record 2657)

Amplitude argument `beta * center - 30 / (1 - center^2)` with the exact
rational column-3 parameters of the record-2624 GO route.  The pin is a
literal of the kernel-evaluated record-2620 chain (20-term Horner base,
20 squaring steps, 320-bit storage rounding, and 400-bit upward radius
rounding); the radius
inflates by at most 2^20 * 1e-78 (supRe pin radius for panel 173 likewise)
-/

/-- Exact real exponent `beta * center - 30 / (1 - center^2)`, panel 173. -/
def ampArg2657P173 : ℚ := (-69342561627914974021134218376820706067468417721830225 / 934812984777778779056031911126152526447425852801024)

/-- Stored center of the certified ball for `exp (ampArg2657P173)`. -/
def ampValue2657P173 : ℚ := (13016692803340876768253385885457125657455949329094067754167372431 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (ampArg2657P173)`. -/
def ampRadius2657P173 : ℚ := (302231456966380561804599 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem ampChain2657P173 :
    compactExp2620 (ampArg2657P173 / (2 : ℚ) ^ 20, 0) 20
      = ((ampValue2657P173, 0), ampRadius2657P173) := by
  decide +kernel

/-- Two-sided pin: `exp(ampArg) in [value - radius, value + radius]`. -/
theorem ampPin2657P173 :
    |Real.exp ((ampArg2657P173 : ℝ)) - (ampValue2657P173 : ℝ)|
      ≤ (ampRadius2657P173 : ℝ) := by
  have harg : ampArg2657P173 = (-69342561627914974021134218376820706067468417721830225 / 934812984777778779056031911126152526447425852801024) := rfl
  have hsmall : |((ampArg2657P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 ampArg2657P173 20 hsmall
  rw [ampChain2657P173] at h
  simpa [embedPair2542] using h

/-- Exact normalized-phase supremum `beta * half + 30/(1-center^2)
- 30/(1-(|center|+half)^2)`, panel 173 (vacuous-VAR budget channel). -/
def supArg2657P173 : ℚ := (-269776008447220725391598841399527100326609966537760575 / 167331524275222401451029712091581302234089227651383296)

/-- Stored center of the certified ball for `exp (supArg2657P173)`. -/
def supValue2657P173 : ℚ := (426008576634409499386634171408992859735976487712792464587217568558965188345810395074959809218231 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576)

/-- Stored radius of the certified ball for `exp (supArg2657P173)`. -/
def supRadius2657P173 : ℚ := (540030858189901188208302654170337551582115176201 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

/-- Kernel evaluation of the record-2620 chain pins the stored ball. -/
theorem supChain2657P173 :
    compactExp2620 (supArg2657P173 / (2 : ℚ) ^ 20, 0) 20
      = ((supValue2657P173, 0), supRadius2657P173) := by
  decide +kernel

/-- Two-sided pin: `exp(supArg) in [value - radius, value + radius]`. -/
theorem supPin2657P173 :
    |Real.exp ((supArg2657P173 : ℝ)) - (supValue2657P173 : ℝ)|
      ≤ (supRadius2657P173 : ℝ) := by
  have harg : supArg2657P173 = (-269776008447220725391598841399527100326609966537760575 / 167331524275222401451029712091581302234089227651383296) := rfl
  have hsmall : |((supArg2657P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    rw [harg]
    norm_num
  have h := compactExp_real_error2620 supArg2657P173 20 hsmall
  rw [supChain2657P173] at h
  simpa [embedPair2542] using h

end ConnesWeilRH.Dev
