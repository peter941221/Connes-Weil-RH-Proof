import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 161 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P161 : ℚ := (802091122136111349402174889339652488944396660425 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P161 : RatPair2542 := ((-382989194710814657907633577407855555815065813708821788902246294276124603939302352262999351671425 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-2101370955913533348630135208142489673058326053996913430781410648293600587011454046324637104356367 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P161 : ℚ := (62922806710427397187569242163492529882665174326213 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P161 :
    phaseExp2646 phaseArg2658P161 20 =
      ((phaseValue2658P161.1,
        phaseValue2658P161.2), phaseRadius2658P161) := by
  decide +kernel

theorem phaseCosPin2658P161 :
    |Real.cos (phaseArg2658P161 : ℝ) -
      (phaseValue2658P161.1 : ℝ)| ≤
        (phaseRadius2658P161 : ℝ) := by
  have hsmall : |((phaseArg2658P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P161]
  have h := phaseExp_cos_error2646 phaseArg2658P161 20 hsmall
  rw [phaseChain2658P161] at h
  simpa [phaseValue2658P161] using h

theorem phaseSinPin2658P161 :
    |Real.sin (phaseArg2658P161 : ℝ) -
      (phaseValue2658P161.2 : ℝ)| ≤
        (phaseRadius2658P161 : ℝ) := by
  have hsmall : |((phaseArg2658P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P161]
  have h := phaseExp_sin_error2646 phaseArg2658P161 20 hsmall
  rw [phaseChain2658P161] at h
  simpa [phaseValue2658P161] using h

end ConnesWeilRH.Dev
