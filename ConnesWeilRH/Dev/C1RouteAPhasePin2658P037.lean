import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 037 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P037 : ℚ := (-693537436433479738204888062210977716004553503375 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P037 : RatPair2542 := ((-1043102825961186246578880046843946695458893870736863096662253368521089632945123363697658499330883 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1863968109194463234071437627607036147467657914539827770906563833990652228298002616169387685158195 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P037 : ℚ := (58046686135227574975889968453383076550210647424523 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P037 :
    phaseExp2646 phaseArg2658P037 20 =
      ((phaseValue2658P037.1,
        phaseValue2658P037.2), phaseRadius2658P037) := by
  decide +kernel

theorem phaseCosPin2658P037 :
    |Real.cos (phaseArg2658P037 : ℝ) -
      (phaseValue2658P037.1 : ℝ)| ≤
        (phaseRadius2658P037 : ℝ) := by
  have hsmall : |((phaseArg2658P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P037]
  have h := phaseExp_cos_error2646 phaseArg2658P037 20 hsmall
  rw [phaseChain2658P037] at h
  simpa [phaseValue2658P037] using h

theorem phaseSinPin2658P037 :
    |Real.sin (phaseArg2658P037 : ℝ) -
      (phaseValue2658P037.2 : ℝ)| ≤
        (phaseRadius2658P037 : ℝ) := by
  have hsmall : |((phaseArg2658P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P037]
  have h := phaseExp_sin_error2646 phaseArg2658P037 20 hsmall
  rw [phaseChain2658P037] at h
  simpa [phaseValue2658P037] using h

end ConnesWeilRH.Dev
