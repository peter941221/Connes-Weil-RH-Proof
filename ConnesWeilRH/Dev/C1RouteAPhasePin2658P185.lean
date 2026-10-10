import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 185 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P185 : ℚ := (1091567617343128979261606428349451883450645079225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P185 : RatPair2542 := ((1375222075500301862463198084186226583889126401852182658703280190607457061828037014003832725070259 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-408595525908479973053691675598743898876915303413851493180371862282971357705530295518427216028463 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P185 : ℚ := (42094632955815343464628855243019016973449589339397 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P185 :
    phaseExp2646 phaseArg2658P185 20 =
      ((phaseValue2658P185.1,
        phaseValue2658P185.2), phaseRadius2658P185) := by
  decide +kernel

theorem phaseCosPin2658P185 :
    |Real.cos (phaseArg2658P185 : ℝ) -
      (phaseValue2658P185.1 : ℝ)| ≤
        (phaseRadius2658P185 : ℝ) := by
  have hsmall : |((phaseArg2658P185 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P185]
  have h := phaseExp_cos_error2646 phaseArg2658P185 20 hsmall
  rw [phaseChain2658P185] at h
  simpa [phaseValue2658P185] using h

theorem phaseSinPin2658P185 :
    |Real.sin (phaseArg2658P185 : ℝ) -
      (phaseValue2658P185.2 : ℝ)| ≤
        (phaseRadius2658P185 : ℝ) := by
  have hsmall : |((phaseArg2658P185 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P185]
  have h := phaseExp_sin_error2646 phaseArg2658P185 20 hsmall
  rw [phaseChain2658P185] at h
  simpa [phaseValue2658P185] using h

end ConnesWeilRH.Dev
