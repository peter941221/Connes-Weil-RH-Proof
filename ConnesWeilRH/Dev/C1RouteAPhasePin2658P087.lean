import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 087 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P087 : ℚ := (-90461404752193009331072355940562310783202630875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P087 : RatPair2542 := ((2055768136269343975181383976273617483776978256151376990663499824329866376866011084391945375334039 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-72484695315832793282007112322238906359598924976983939423007479439187062207475326874846382570855 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P087 : ℚ := (1083526019846711628958373202874159810276393614565 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P087 :
    phaseExp2646 phaseArg2658P087 20 =
      ((phaseValue2658P087.1,
        phaseValue2658P087.2), phaseRadius2658P087) := by
  decide +kernel

theorem phaseCosPin2658P087 :
    |Real.cos (phaseArg2658P087 : ℝ) -
      (phaseValue2658P087.1 : ℝ)| ≤
        (phaseRadius2658P087 : ℝ) := by
  have hsmall : |((phaseArg2658P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P087]
  have h := phaseExp_cos_error2646 phaseArg2658P087 20 hsmall
  rw [phaseChain2658P087] at h
  simpa [phaseValue2658P087] using h

theorem phaseSinPin2658P087 :
    |Real.sin (phaseArg2658P087 : ℝ) -
      (phaseValue2658P087.2 : ℝ)| ≤
        (phaseRadius2658P087 : ℝ) := by
  have hsmall : |((phaseArg2658P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P087]
  have h := phaseExp_sin_error2646 phaseArg2658P087 20 hsmall
  rw [phaseChain2658P087] at h
  simpa [phaseValue2658P087] using h

end ConnesWeilRH.Dev
