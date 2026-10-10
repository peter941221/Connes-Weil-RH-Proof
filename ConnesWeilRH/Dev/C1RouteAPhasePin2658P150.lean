import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 150 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P150 : ℚ := (669414395166228269049935433960161099795699468475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P150 : RatPair2542 := ((-477660084208142022758559034467498445259716153982222722144719178985449066325501666203693276358647 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1910446019504157020260575898818038505979730570296354031534755355511250955749107638771573327077611 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P150 : ℚ := (30171830713067272797648946464865717868237294616837 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P150 :
    phaseExp2646 phaseArg2658P150 20 =
      ((phaseValue2658P150.1,
        phaseValue2658P150.2), phaseRadius2658P150) := by
  decide +kernel

theorem phaseCosPin2658P150 :
    |Real.cos (phaseArg2658P150 : ℝ) -
      (phaseValue2658P150.1 : ℝ)| ≤
        (phaseRadius2658P150 : ℝ) := by
  have hsmall : |((phaseArg2658P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P150]
  have h := phaseExp_cos_error2646 phaseArg2658P150 20 hsmall
  rw [phaseChain2658P150] at h
  simpa [phaseValue2658P150] using h

theorem phaseSinPin2658P150 :
    |Real.sin (phaseArg2658P150 : ℝ) -
      (phaseValue2658P150.2 : ℝ)| ≤
        (phaseRadius2658P150 : ℝ) := by
  have hsmall : |((phaseArg2658P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P150]
  have h := phaseExp_sin_error2646 phaseArg2658P150 20 hsmall
  rw [phaseChain2658P150] at h
  simpa [phaseValue2658P150] using h

end ConnesWeilRH.Dev
