import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 118 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P118 : ℚ := (283445734890204762570693381947095240454034910075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P118 : RatPair2542 := ((353996155745485833870289329275628064581961933037694323707856221314155102069777642825117929996883 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-1007619410354408834474931248281387539992348715134328936449374157342037145538435667526425222983401 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P118 : ℚ := (3992016384064757065687312875268051540196209615889 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P118 :
    phaseExp2646 phaseArg2658P118 20 =
      ((phaseValue2658P118.1,
        phaseValue2658P118.2), phaseRadius2658P118) := by
  decide +kernel

theorem phaseCosPin2658P118 :
    |Real.cos (phaseArg2658P118 : ℝ) -
      (phaseValue2658P118.1 : ℝ)| ≤
        (phaseRadius2658P118 : ℝ) := by
  have hsmall : |((phaseArg2658P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P118]
  have h := phaseExp_cos_error2646 phaseArg2658P118 20 hsmall
  rw [phaseChain2658P118] at h
  simpa [phaseValue2658P118] using h

theorem phaseSinPin2658P118 :
    |Real.sin (phaseArg2658P118 : ℝ) -
      (phaseValue2658P118.2 : ℝ)| ≤
        (phaseRadius2658P118 : ℝ) := by
  have hsmall : |((phaseArg2658P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P118]
  have h := phaseExp_sin_error2646 phaseArg2658P118 20 hsmall
  rw [phaseChain2658P118] at h
  simpa [phaseValue2658P118] using h

end ConnesWeilRH.Dev
