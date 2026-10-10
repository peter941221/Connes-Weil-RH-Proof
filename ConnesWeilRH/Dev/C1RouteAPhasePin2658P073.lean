import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 073 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P073 : ℚ := (-259322693622953293415740753696278624245180875175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P073 : RatPair2542 := ((-516177402263800481758516282383307355787114939986996012118846714757519043080394466064067470848439 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (-547188128432361404491295617345844885291007853356855358796823217964912124908986734698169990026521 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P073 : ℚ := (27246057361055028439744327953986621842357604755141 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P073 :
    phaseExp2646 phaseArg2658P073 20 =
      ((phaseValue2658P073.1,
        phaseValue2658P073.2), phaseRadius2658P073) := by
  decide +kernel

theorem phaseCosPin2658P073 :
    |Real.cos (phaseArg2658P073 : ℝ) -
      (phaseValue2658P073.1 : ℝ)| ≤
        (phaseRadius2658P073 : ℝ) := by
  have hsmall : |((phaseArg2658P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P073]
  have h := phaseExp_cos_error2646 phaseArg2658P073 20 hsmall
  rw [phaseChain2658P073] at h
  simpa [phaseValue2658P073] using h

theorem phaseSinPin2658P073 :
    |Real.sin (phaseArg2658P073 : ℝ) -
      (phaseValue2658P073.2 : ℝ)| ≤
        (phaseRadius2658P073 : ℝ) := by
  have hsmall : |((phaseArg2658P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P073]
  have h := phaseExp_sin_error2646 phaseArg2658P073 20 hsmall
  rw [phaseChain2658P073] at h
  simpa [phaseValue2658P073] using h

end ConnesWeilRH.Dev
