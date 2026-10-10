import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 098 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P098 : ℚ := (42215322217690071021167099438929078365494561075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P098 : RatPair2542 := ((-323974530546623771082446961252582475718121138003993332123760629548794714371153444140344275854389 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (1697966040454199153273314855099308494165280535166663532268503167599669462372942999910553054937167 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P098 : ℚ := (8638068462715049410910699393197009456377774959053 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P098 :
    phaseExp2646 phaseArg2658P098 20 =
      ((phaseValue2658P098.1,
        phaseValue2658P098.2), phaseRadius2658P098) := by
  decide +kernel

theorem phaseCosPin2658P098 :
    |Real.cos (phaseArg2658P098 : ℝ) -
      (phaseValue2658P098.1 : ℝ)| ≤
        (phaseRadius2658P098 : ℝ) := by
  have hsmall : |((phaseArg2658P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P098]
  have h := phaseExp_cos_error2646 phaseArg2658P098 20 hsmall
  rw [phaseChain2658P098] at h
  simpa [phaseValue2658P098] using h

theorem phaseSinPin2658P098 :
    |Real.sin (phaseArg2658P098 : ℝ) -
      (phaseValue2658P098.2 : ℝ)| ≤
        (phaseRadius2658P098 : ℝ) := by
  have hsmall : |((phaseArg2658P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P098]
  have h := phaseExp_sin_error2646 phaseArg2658P098 20 hsmall
  rw [phaseChain2658P098] at h
  simpa [phaseValue2658P098] using h

end ConnesWeilRH.Dev
