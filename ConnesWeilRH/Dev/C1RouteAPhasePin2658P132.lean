import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 132 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P132 : ℚ := (452307023760965046655361779702811553916013154375 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P132 : RatPair2542 := ((208140479408981928511340578492097480244289315343379950949531593818625944688192254147140866659167 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1047515009552105642040885389224945572598045637315550663648861137497719334306182813908275317150975 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P132 : ℚ := (45814454322831645635046446192083759489879281321389 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P132 :
    phaseExp2646 phaseArg2658P132 20 =
      ((phaseValue2658P132.1,
        phaseValue2658P132.2), phaseRadius2658P132) := by
  decide +kernel

theorem phaseCosPin2658P132 :
    |Real.cos (phaseArg2658P132 : ℝ) -
      (phaseValue2658P132.1 : ℝ)| ≤
        (phaseRadius2658P132 : ℝ) := by
  have hsmall : |((phaseArg2658P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P132]
  have h := phaseExp_cos_error2646 phaseArg2658P132 20 hsmall
  rw [phaseChain2658P132] at h
  simpa [phaseValue2658P132] using h

theorem phaseSinPin2658P132 :
    |Real.sin (phaseArg2658P132 : ℝ) -
      (phaseValue2658P132.2 : ℝ)| ≤
        (phaseRadius2658P132 : ℝ) := by
  have hsmall : |((phaseArg2658P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P132]
  have h := phaseExp_sin_error2646 phaseArg2658P132 20 hsmall
  rw [phaseChain2658P132] at h
  simpa [phaseValue2658P132] using h

end ConnesWeilRH.Dev
