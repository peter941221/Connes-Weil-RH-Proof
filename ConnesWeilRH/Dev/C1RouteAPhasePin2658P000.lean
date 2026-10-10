import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 000 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P000 : ℚ := (-1139813699877631917571511684851085115868353149025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P000 : RatPair2542 := ((-1012924128679806094771362911102117148442112470761301060960037802330803271876364207177508838503601 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (677037263210244370039554614453007511183433522289680059085295539158885017176145644469502345778083 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P000 : ℚ := (9911972813746497235337850630085523035777095070537 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P000 :
    phaseExp2646 phaseArg2658P000 20 =
      ((phaseValue2658P000.1,
        phaseValue2658P000.2), phaseRadius2658P000) := by
  decide +kernel

theorem phaseCosPin2658P000 :
    |Real.cos (phaseArg2658P000 : ℝ) -
      (phaseValue2658P000.1 : ℝ)| ≤
        (phaseRadius2658P000 : ℝ) := by
  have hsmall : |((phaseArg2658P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P000]
  have h := phaseExp_cos_error2646 phaseArg2658P000 20 hsmall
  rw [phaseChain2658P000] at h
  simpa [phaseValue2658P000] using h

theorem phaseSinPin2658P000 :
    |Real.sin (phaseArg2658P000 : ℝ) -
      (phaseValue2658P000.2 : ℝ)| ≤
        (phaseRadius2658P000 : ℝ) := by
  have hsmall : |((phaseArg2658P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P000]
  have h := phaseExp_sin_error2646 phaseArg2658P000 20 hsmall
  rw [phaseChain2658P000] at h
  simpa [phaseValue2658P000] using h

end ConnesWeilRH.Dev
