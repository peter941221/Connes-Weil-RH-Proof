import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 054 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P054 : ℚ := (-488491585661842250387790722079036478229294206725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P054 : RatPair2542 := ((91917723083796160943790441744396378261246492801257226243809049630715069114522038926458261472523 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-66501917459099422143918765669232989244493646967349645035098941397977992298600498586605897346185 / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768))
def phaseRadius2658P054 : ℚ := (11752294485438849308358682434257792827508524195193 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P054 :
    phaseExp2646 phaseArg2658P054 20 =
      ((phaseValue2658P054.1,
        phaseValue2658P054.2), phaseRadius2658P054) := by
  decide +kernel

theorem phaseCosPin2658P054 :
    |Real.cos (phaseArg2658P054 : ℝ) -
      (phaseValue2658P054.1 : ℝ)| ≤
        (phaseRadius2658P054 : ℝ) := by
  have hsmall : |((phaseArg2658P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P054]
  have h := phaseExp_cos_error2646 phaseArg2658P054 20 hsmall
  rw [phaseChain2658P054] at h
  simpa [phaseValue2658P054] using h

theorem phaseSinPin2658P054 :
    |Real.sin (phaseArg2658P054 : ℝ) -
      (phaseValue2658P054.2 : ℝ)| ≤
        (phaseRadius2658P054 : ℝ) := by
  have hsmall : |((phaseArg2658P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P054]
  have h := phaseExp_sin_error2646 phaseArg2658P054 20 hsmall
  rw [phaseChain2658P054] at h
  simpa [phaseValue2658P054] using h

end ConnesWeilRH.Dev
