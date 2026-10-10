import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 002 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P002 : ℚ := (-1115690658610380448416559056600268499659499114125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P002 : RatPair2542 := ((144688435310511314067703005218962149068977062538634263854329909779304875045114514697975038906511 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (-2056084804822148123271326368559452973164682033083282138066917933957778114296380514499820529326125 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P002 : ℚ := (8428852498523815158290364261319943752488434274949 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P002 :
    phaseExp2646 phaseArg2658P002 20 =
      ((phaseValue2658P002.1,
        phaseValue2658P002.2), phaseRadius2658P002) := by
  decide +kernel

theorem phaseCosPin2658P002 :
    |Real.cos (phaseArg2658P002 : ℝ) -
      (phaseValue2658P002.1 : ℝ)| ≤
        (phaseRadius2658P002 : ℝ) := by
  have hsmall : |((phaseArg2658P002 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P002]
  have h := phaseExp_cos_error2646 phaseArg2658P002 20 hsmall
  rw [phaseChain2658P002] at h
  simpa [phaseValue2658P002] using h

theorem phaseSinPin2658P002 :
    |Real.sin (phaseArg2658P002 : ℝ) -
      (phaseValue2658P002.2 : ℝ)| ≤
        (phaseRadius2658P002 : ℝ) := by
  have hsmall : |((phaseArg2658P002 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P002]
  have h := phaseExp_sin_error2646 phaseArg2658P002 20 hsmall
  rw [phaseChain2658P002] at h
  simpa [phaseValue2658P002] using h

end ConnesWeilRH.Dev
