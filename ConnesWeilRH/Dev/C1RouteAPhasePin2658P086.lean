import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 086 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P086 : ℚ := (-102522925385818743908548670065970618887629648325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P086 : RatPair2542 := ((-449467928335015987966639184089604375910778518677826295235655184909007137687035143785000333853187 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (2088161679329554249401550624810522268373109279642582058526747188343019681238536594520048085436887 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P086 : ℚ := (25122967905684723159398264284424186908706871961541 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P086 :
    phaseExp2646 phaseArg2658P086 20 =
      ((phaseValue2658P086.1,
        phaseValue2658P086.2), phaseRadius2658P086) := by
  decide +kernel

theorem phaseCosPin2658P086 :
    |Real.cos (phaseArg2658P086 : ℝ) -
      (phaseValue2658P086.1 : ℝ)| ≤
        (phaseRadius2658P086 : ℝ) := by
  have hsmall : |((phaseArg2658P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P086]
  have h := phaseExp_cos_error2646 phaseArg2658P086 20 hsmall
  rw [phaseChain2658P086] at h
  simpa [phaseValue2658P086] using h

theorem phaseSinPin2658P086 :
    |Real.sin (phaseArg2658P086 : ℝ) -
      (phaseValue2658P086.2 : ℝ)| ≤
        (phaseRadius2658P086 : ℝ) := by
  have hsmall : |((phaseArg2658P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P086]
  have h := phaseExp_sin_error2646 phaseArg2658P086 20 hsmall
  rw [phaseChain2658P086] at h
  simpa [phaseValue2658P086] using h

end ConnesWeilRH.Dev
