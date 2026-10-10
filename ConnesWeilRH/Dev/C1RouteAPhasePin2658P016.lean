import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 016 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P016 : ℚ := (-946829369739620164331890658844552186197520869825 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P016 : RatPair2542 := ((548316668968132721523731245050957931413740682905386644174861099215085754138051629707162056744091 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (2064410193773002656844329273591047272998876525925505816014052223097845961799198612026373627410093 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P016 : ℚ := (63998729627331021779147443145909212116008212148811 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P016 :
    phaseExp2646 phaseArg2658P016 20 =
      ((phaseValue2658P016.1,
        phaseValue2658P016.2), phaseRadius2658P016) := by
  decide +kernel

theorem phaseCosPin2658P016 :
    |Real.cos (phaseArg2658P016 : ℝ) -
      (phaseValue2658P016.1 : ℝ)| ≤
        (phaseRadius2658P016 : ℝ) := by
  have hsmall : |((phaseArg2658P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P016]
  have h := phaseExp_cos_error2646 phaseArg2658P016 20 hsmall
  rw [phaseChain2658P016] at h
  simpa [phaseValue2658P016] using h

theorem phaseSinPin2658P016 :
    |Real.sin (phaseArg2658P016 : ℝ) -
      (phaseValue2658P016.2 : ℝ)| ≤
        (phaseRadius2658P016 : ℝ) := by
  have hsmall : |((phaseArg2658P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P016]
  have h := phaseExp_sin_error2646 phaseArg2658P016 20 hsmall
  rw [phaseChain2658P016] at h
  simpa [phaseValue2658P016] using h

end ConnesWeilRH.Dev
