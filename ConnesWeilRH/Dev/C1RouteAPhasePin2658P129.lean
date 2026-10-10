import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 129 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P129 : ℚ := (416122461860087842922932837326586629602732102025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P129 : RatPair2542 := ((321848547324881755325949507429952209175321016773115118849569548510168565024873226146661475336309 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (254585897462724277291270173569644750376536455294983369782109810730446421767201318859796001915619 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P129 : ℚ := (39922298608012202320126493761777591811552620819781 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P129 :
    phaseExp2646 phaseArg2658P129 20 =
      ((phaseValue2658P129.1,
        phaseValue2658P129.2), phaseRadius2658P129) := by
  decide +kernel

theorem phaseCosPin2658P129 :
    |Real.cos (phaseArg2658P129 : ℝ) -
      (phaseValue2658P129.1 : ℝ)| ≤
        (phaseRadius2658P129 : ℝ) := by
  have hsmall : |((phaseArg2658P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P129]
  have h := phaseExp_cos_error2646 phaseArg2658P129 20 hsmall
  rw [phaseChain2658P129] at h
  simpa [phaseValue2658P129] using h

theorem phaseSinPin2658P129 :
    |Real.sin (phaseArg2658P129 : ℝ) -
      (phaseValue2658P129.2 : ℝ)| ≤
        (phaseRadius2658P129 : ℝ) := by
  have hsmall : |((phaseArg2658P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P129]
  have h := phaseExp_sin_error2646 phaseArg2658P129 20 hsmall
  rw [phaseChain2658P129] at h
  simpa [phaseValue2658P129] using h

end ConnesWeilRH.Dev
