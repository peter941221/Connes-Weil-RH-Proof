import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 038 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P038 : ℚ := (-681475915799854003627411748085569407900126485925 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P038 : RatPair2542 := ((533852397662739665520152823114037864902091768902880838858663916645127218412202687957263986326437 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (24831923898987261194484559534259912313093043047669710056508352133378084513457809451267946258627 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P038 : ℚ := (6197578081029261998676985893209660600918603724067 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P038 :
    phaseExp2646 phaseArg2658P038 20 =
      ((phaseValue2658P038.1,
        phaseValue2658P038.2), phaseRadius2658P038) := by
  decide +kernel

theorem phaseCosPin2658P038 :
    |Real.cos (phaseArg2658P038 : ℝ) -
      (phaseValue2658P038.1 : ℝ)| ≤
        (phaseRadius2658P038 : ℝ) := by
  have hsmall : |((phaseArg2658P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P038]
  have h := phaseExp_cos_error2646 phaseArg2658P038 20 hsmall
  rw [phaseChain2658P038] at h
  simpa [phaseValue2658P038] using h

theorem phaseSinPin2658P038 :
    |Real.sin (phaseArg2658P038 : ℝ) -
      (phaseValue2658P038.2 : ℝ)| ≤
        (phaseRadius2658P038 : ℝ) := by
  have hsmall : |((phaseArg2658P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P038]
  have h := phaseExp_sin_error2646 phaseArg2658P038 20 hsmall
  rw [phaseChain2658P038] at h
  simpa [phaseValue2658P038] using h

end ConnesWeilRH.Dev
