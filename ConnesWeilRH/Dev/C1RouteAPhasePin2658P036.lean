import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 036 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P036 : ℚ := (-705598957067105472782364376336386024108980520825 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P036 : RatPair2542 := ((-1159221845673426175363880636590702889314041525537458444583367278633811578977037194209998846635161 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1794058340783735640843263971418612653779619255280565801261277687176636257725374952597007627739039 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P036 : ℚ := (48567187463421515825713799921105729551483012251945 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P036 :
    phaseExp2646 phaseArg2658P036 20 =
      ((phaseValue2658P036.1,
        phaseValue2658P036.2), phaseRadius2658P036) := by
  decide +kernel

theorem phaseCosPin2658P036 :
    |Real.cos (phaseArg2658P036 : ℝ) -
      (phaseValue2658P036.1 : ℝ)| ≤
        (phaseRadius2658P036 : ℝ) := by
  have hsmall : |((phaseArg2658P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P036]
  have h := phaseExp_cos_error2646 phaseArg2658P036 20 hsmall
  rw [phaseChain2658P036] at h
  simpa [phaseValue2658P036] using h

theorem phaseSinPin2658P036 :
    |Real.sin (phaseArg2658P036 : ℝ) -
      (phaseValue2658P036.2 : ℝ)| ≤
        (phaseRadius2658P036 : ℝ) := by
  have hsmall : |((phaseArg2658P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P036]
  have h := phaseExp_sin_error2646 phaseArg2658P036 20 hsmall
  rw [phaseChain2658P036] at h
  simpa [phaseValue2658P036] using h

end ConnesWeilRH.Dev
