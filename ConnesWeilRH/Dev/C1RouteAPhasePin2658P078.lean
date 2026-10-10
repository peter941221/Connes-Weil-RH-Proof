import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 078 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P078 : ℚ := (-199015090454824620528359183069237083723045787925 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P078 : RatPair2542 := ((1757039940319429595851503446781129316413387380347275031611917523698110598238401732085588047711591 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1214599220214013846738282395041593298672621134489605354384886403505160386720776924880643825438457 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P078 : ℚ := (28556064829356280518235097533744789460045735793985 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P078 :
    phaseExp2646 phaseArg2658P078 20 =
      ((phaseValue2658P078.1,
        phaseValue2658P078.2), phaseRadius2658P078) := by
  decide +kernel

theorem phaseCosPin2658P078 :
    |Real.cos (phaseArg2658P078 : ℝ) -
      (phaseValue2658P078.1 : ℝ)| ≤
        (phaseRadius2658P078 : ℝ) := by
  have hsmall : |((phaseArg2658P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P078]
  have h := phaseExp_cos_error2646 phaseArg2658P078 20 hsmall
  rw [phaseChain2658P078] at h
  simpa [phaseValue2658P078] using h

theorem phaseSinPin2658P078 :
    |Real.sin (phaseArg2658P078 : ℝ) -
      (phaseValue2658P078.2 : ℝ)| ≤
        (phaseRadius2658P078 : ℝ) := by
  have hsmall : |((phaseArg2658P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P078]
  have h := phaseExp_sin_error2646 phaseArg2658P078 20 hsmall
  rw [phaseChain2658P078] at h
  simpa [phaseValue2658P078] using h

end ConnesWeilRH.Dev
