import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 026 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P026 : ℚ := (-826214163403362818557127517590469105153250695325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P026 : RatPair2542 := ((976632753619859575312905444252221723655627346696737327740314520986773883129668731120229108638203 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-216101029013306336600583362473018684982089886441344943710648881182889894709957431571597113360005 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P026 : ℚ := (4128435652417330970834849461955845789022014151665 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P026 :
    phaseExp2646 phaseArg2658P026 20 =
      ((phaseValue2658P026.1,
        phaseValue2658P026.2), phaseRadius2658P026) := by
  decide +kernel

theorem phaseCosPin2658P026 :
    |Real.cos (phaseArg2658P026 : ℝ) -
      (phaseValue2658P026.1 : ℝ)| ≤
        (phaseRadius2658P026 : ℝ) := by
  have hsmall : |((phaseArg2658P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P026]
  have h := phaseExp_cos_error2646 phaseArg2658P026 20 hsmall
  rw [phaseChain2658P026] at h
  simpa [phaseValue2658P026] using h

theorem phaseSinPin2658P026 :
    |Real.sin (phaseArg2658P026 : ℝ) -
      (phaseValue2658P026.2 : ℝ)| ≤
        (phaseRadius2658P026 : ℝ) := by
  have hsmall : |((phaseArg2658P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P026]
  have h := phaseExp_sin_error2646 phaseArg2658P026 20 hsmall
  rw [phaseChain2658P026] at h
  simpa [phaseValue2658P026] using h

end ConnesWeilRH.Dev
