import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 111 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P111 : ℚ := (199015090454824620528359183069237083723045787925 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P111 : RatPair2542 := ((878519970159714797925751723390564658206693690173637515805958761849055299119200866042794024452721 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (607299610107006923369141197520796649336310567244802677192443201752580193360388462440321911856007 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P111 : ℚ := (28556064829356280518235097533744789460045735793985 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P111 :
    phaseExp2646 phaseArg2658P111 20 =
      ((phaseValue2658P111.1,
        phaseValue2658P111.2), phaseRadius2658P111) := by
  decide +kernel

theorem phaseCosPin2658P111 :
    |Real.cos (phaseArg2658P111 : ℝ) -
      (phaseValue2658P111.1 : ℝ)| ≤
        (phaseRadius2658P111 : ℝ) := by
  have hsmall : |((phaseArg2658P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P111]
  have h := phaseExp_cos_error2646 phaseArg2658P111 20 hsmall
  rw [phaseChain2658P111] at h
  simpa [phaseValue2658P111] using h

theorem phaseSinPin2658P111 :
    |Real.sin (phaseArg2658P111 : ℝ) -
      (phaseValue2658P111.2 : ℝ)| ≤
        (phaseRadius2658P111 : ℝ) := by
  have hsmall : |((phaseArg2658P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P111]
  have h := phaseExp_sin_error2646 phaseArg2658P111 20 hsmall
  rw [phaseChain2658P111] at h
  simpa [phaseValue2658P111] using h

end ConnesWeilRH.Dev
