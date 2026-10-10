import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 125 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P125 : ℚ := (367876379325584904613027580824953397185024032225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P125 : RatPair2542 := ((-1065313930312008189782782424447160363474168790339932216672933050890859026381631419241041820840487 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-151213548185743764903327611067804963253179610229929829242049011632547916877545698092182590802289 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P125 : ℚ := (16520547236984196707695929397184855812747712739633 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P125 :
    phaseExp2646 phaseArg2658P125 20 =
      ((phaseValue2658P125.1,
        phaseValue2658P125.2), phaseRadius2658P125) := by
  decide +kernel

theorem phaseCosPin2658P125 :
    |Real.cos (phaseArg2658P125 : ℝ) -
      (phaseValue2658P125.1 : ℝ)| ≤
        (phaseRadius2658P125 : ℝ) := by
  have hsmall : |((phaseArg2658P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P125]
  have h := phaseExp_cos_error2646 phaseArg2658P125 20 hsmall
  rw [phaseChain2658P125] at h
  simpa [phaseValue2658P125] using h

theorem phaseSinPin2658P125 :
    |Real.sin (phaseArg2658P125 : ℝ) -
      (phaseValue2658P125.2 : ℝ)| ≤
        (phaseRadius2658P125 : ℝ) := by
  have hsmall : |((phaseArg2658P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P125]
  have h := phaseExp_sin_error2646 phaseArg2658P125 20 hsmall
  rw [phaseChain2658P125] at h
  simpa [phaseValue2658P125] using h

end ConnesWeilRH.Dev
