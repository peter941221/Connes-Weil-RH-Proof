import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 141 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P141 : ℚ := (560860709463596657852648606831486326855856311425 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P141 : RatPair2542 := ((-284883538657788454998007050908300433429458503322013612903337596510480454097536643624417906643883 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1058451934079201771475130372869750171718241992676077883464340807108607998614767471438039037828615 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P141 : ℚ := (14049551274616795582053412067981333044812670480355 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P141 :
    phaseExp2646 phaseArg2658P141 20 =
      ((phaseValue2658P141.1,
        phaseValue2658P141.2), phaseRadius2658P141) := by
  decide +kernel

theorem phaseCosPin2658P141 :
    |Real.cos (phaseArg2658P141 : ℝ) -
      (phaseValue2658P141.1 : ℝ)| ≤
        (phaseRadius2658P141 : ℝ) := by
  have hsmall : |((phaseArg2658P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P141]
  have h := phaseExp_cos_error2646 phaseArg2658P141 20 hsmall
  rw [phaseChain2658P141] at h
  simpa [phaseValue2658P141] using h

theorem phaseSinPin2658P141 :
    |Real.sin (phaseArg2658P141 : ℝ) -
      (phaseValue2658P141.2 : ℝ)| ≤
        (phaseRadius2658P141 : ℝ) := by
  have hsmall : |((phaseArg2658P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P141]
  have h := phaseExp_sin_error2646 phaseArg2658P141 20 hsmall
  rw [phaseChain2658P141] at h
  simpa [phaseValue2658P141] using h

end ConnesWeilRH.Dev
