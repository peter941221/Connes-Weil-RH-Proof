import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 070 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P070 : ℚ := (-295507255523830497148169696072503548558461927525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P070 : RatPair2542 := ((-1056145625669089171830483103127387929908214439336200658387218483138253867372264904387870723361193 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-39659938686284059929036311901622443860711122464701772292249115326667751938625465120063731491199 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P070 : ℚ := (18725156341073625938548163164640223323824193332177 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P070 :
    phaseExp2646 phaseArg2658P070 20 =
      ((phaseValue2658P070.1,
        phaseValue2658P070.2), phaseRadius2658P070) := by
  decide +kernel

theorem phaseCosPin2658P070 :
    |Real.cos (phaseArg2658P070 : ℝ) -
      (phaseValue2658P070.1 : ℝ)| ≤
        (phaseRadius2658P070 : ℝ) := by
  have hsmall : |((phaseArg2658P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P070]
  have h := phaseExp_cos_error2646 phaseArg2658P070 20 hsmall
  rw [phaseChain2658P070] at h
  simpa [phaseValue2658P070] using h

theorem phaseSinPin2658P070 :
    |Real.sin (phaseArg2658P070 : ℝ) -
      (phaseValue2658P070.2 : ℝ)| ≤
        (phaseRadius2658P070 : ℝ) := by
  have hsmall : |((phaseArg2658P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P070]
  have h := phaseExp_sin_error2646 phaseArg2658P070 20 hsmall
  rw [phaseChain2658P070] at h
  simpa [phaseValue2658P070] using h

end ConnesWeilRH.Dev
