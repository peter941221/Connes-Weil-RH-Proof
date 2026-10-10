import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 182 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P182 : ℚ := (1055383055442251775529177485973226959137364026875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P182 : RatPair2542 := ((1187540139068354174582777136135557132748659732802567206725175296334926152370025887935184995356661 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-443860129694853114832603805953936603749899589867352046371971831729942644555513938744176500219723 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P182 : ℚ := (53394581041629884649982221062803631444305478528273 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P182 :
    phaseExp2646 phaseArg2658P182 20 =
      ((phaseValue2658P182.1,
        phaseValue2658P182.2), phaseRadius2658P182) := by
  decide +kernel

theorem phaseCosPin2658P182 :
    |Real.cos (phaseArg2658P182 : ℝ) -
      (phaseValue2658P182.1 : ℝ)| ≤
        (phaseRadius2658P182 : ℝ) := by
  have hsmall : |((phaseArg2658P182 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P182]
  have h := phaseExp_cos_error2646 phaseArg2658P182 20 hsmall
  rw [phaseChain2658P182] at h
  simpa [phaseValue2658P182] using h

theorem phaseSinPin2658P182 :
    |Real.sin (phaseArg2658P182 : ℝ) -
      (phaseValue2658P182.2 : ℝ)| ≤
        (phaseRadius2658P182 : ℝ) := by
  have hsmall : |((phaseArg2658P182 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P182]
  have h := phaseExp_sin_error2646 phaseArg2658P182 20 hsmall
  rw [phaseChain2658P182] at h
  simpa [phaseValue2658P182] using h

end ConnesWeilRH.Dev
