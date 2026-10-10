import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 071 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P071 : ℚ := (-283445734890204762570693381947095240454034910075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P071 : RatPair2542 := ((707992311490971667740578658551256129163923866075388647415712442628310204139555285650235861975017 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (503809705177204417237465624140693769996174357567164468224687078671018572769217833763212611320257 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P071 : ℚ := (3992016384064757065687312875268051540196209615889 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P071 :
    phaseExp2646 phaseArg2658P071 20 =
      ((phaseValue2658P071.1,
        phaseValue2658P071.2), phaseRadius2658P071) := by
  decide +kernel

theorem phaseCosPin2658P071 :
    |Real.cos (phaseArg2658P071 : ℝ) -
      (phaseValue2658P071.1 : ℝ)| ≤
        (phaseRadius2658P071 : ℝ) := by
  have hsmall : |((phaseArg2658P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P071]
  have h := phaseExp_cos_error2646 phaseArg2658P071 20 hsmall
  rw [phaseChain2658P071] at h
  simpa [phaseValue2658P071] using h

theorem phaseSinPin2658P071 :
    |Real.sin (phaseArg2658P071 : ℝ) -
      (phaseValue2658P071.2 : ℝ)| ≤
        (phaseRadius2658P071 : ℝ) := by
  have hsmall : |((phaseArg2658P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P071]
  have h := phaseExp_sin_error2646 phaseArg2658P071 20 hsmall
  rw [phaseChain2658P071] at h
  simpa [phaseValue2658P071] using h

end ConnesWeilRH.Dev
