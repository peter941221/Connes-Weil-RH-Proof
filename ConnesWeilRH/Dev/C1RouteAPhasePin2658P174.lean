import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 174 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P174 : ℚ := (958890890373245898909366972969960494301947887275 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P174 : RatPair2542 := ((-2081031124235824728118335381893680267138761142206309565284151122633755783647966998419386907063987 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (120351069164334453301386320947429325768723245062444372702467966544947825844918786045558285391309 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P174 : ℚ := (14316274521101012571812059360092715156739379547839 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P174 :
    phaseExp2646 phaseArg2658P174 20 =
      ((phaseValue2658P174.1,
        phaseValue2658P174.2), phaseRadius2658P174) := by
  decide +kernel

theorem phaseCosPin2658P174 :
    |Real.cos (phaseArg2658P174 : ℝ) -
      (phaseValue2658P174.1 : ℝ)| ≤
        (phaseRadius2658P174 : ℝ) := by
  have hsmall : |((phaseArg2658P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P174]
  have h := phaseExp_cos_error2646 phaseArg2658P174 20 hsmall
  rw [phaseChain2658P174] at h
  simpa [phaseValue2658P174] using h

theorem phaseSinPin2658P174 :
    |Real.sin (phaseArg2658P174 : ℝ) -
      (phaseValue2658P174.2 : ℝ)| ≤
        (phaseRadius2658P174 : ℝ) := by
  have hsmall : |((phaseArg2658P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P174]
  have h := phaseExp_sin_error2646 phaseArg2658P174 20 hsmall
  rw [phaseChain2658P174] at h
  simpa [phaseValue2658P174] using h

end ConnesWeilRH.Dev
