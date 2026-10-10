import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 144 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P144 : ℚ := (597045271364473861585077549207711251169137363775 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P144 : RatPair2542 := ((-515494094125295418001211546850404336281668073749616490415210309072113502285570715199697280325939 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (2072849839362257394932424376460824531129432606133071587998327700379381322705590847391954421018509 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P144 : ℚ := (36605374433808447516527718476748743779183411630177 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P144 :
    phaseExp2646 phaseArg2658P144 20 =
      ((phaseValue2658P144.1,
        phaseValue2658P144.2), phaseRadius2658P144) := by
  decide +kernel

theorem phaseCosPin2658P144 :
    |Real.cos (phaseArg2658P144 : ℝ) -
      (phaseValue2658P144.1 : ℝ)| ≤
        (phaseRadius2658P144 : ℝ) := by
  have hsmall : |((phaseArg2658P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P144]
  have h := phaseExp_cos_error2646 phaseArg2658P144 20 hsmall
  rw [phaseChain2658P144] at h
  simpa [phaseValue2658P144] using h

theorem phaseSinPin2658P144 :
    |Real.sin (phaseArg2658P144 : ℝ) -
      (phaseValue2658P144.2 : ℝ)| ≤
        (phaseRadius2658P144 : ℝ) := by
  have hsmall : |((phaseArg2658P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P144]
  have h := phaseExp_sin_error2646 phaseArg2658P144 20 hsmall
  rw [phaseChain2658P144] at h
  simpa [phaseValue2658P144] using h

end ConnesWeilRH.Dev
