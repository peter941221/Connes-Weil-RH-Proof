import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 050 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P050 : ℚ := (-536737668196345188697695978580669710647002276525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P050 : RatPair2542 := ((477741984038590640772885034047042822766632501212741310180651001616159545572174451166731041805379 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (954275727770612064331633358676691451802063233109461532719868514535194527036886423540462998473097 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P050 : ℚ := (5804529889156330934014193373762290909607222754889 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P050 :
    phaseExp2646 phaseArg2658P050 20 =
      ((phaseValue2658P050.1,
        phaseValue2658P050.2), phaseRadius2658P050) := by
  decide +kernel

theorem phaseCosPin2658P050 :
    |Real.cos (phaseArg2658P050 : ℝ) -
      (phaseValue2658P050.1 : ℝ)| ≤
        (phaseRadius2658P050 : ℝ) := by
  have hsmall : |((phaseArg2658P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P050]
  have h := phaseExp_cos_error2646 phaseArg2658P050 20 hsmall
  rw [phaseChain2658P050] at h
  simpa [phaseValue2658P050] using h

theorem phaseSinPin2658P050 :
    |Real.sin (phaseArg2658P050 : ℝ) -
      (phaseValue2658P050.2 : ℝ)| ≤
        (phaseRadius2658P050 : ℝ) := by
  have hsmall : |((phaseArg2658P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P050]
  have h := phaseExp_sin_error2646 phaseArg2658P050 20 hsmall
  rw [phaseChain2658P050] at h
  simpa [phaseValue2658P050] using h

end ConnesWeilRH.Dev
