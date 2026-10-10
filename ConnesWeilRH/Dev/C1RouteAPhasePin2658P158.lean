import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 158 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P158 : ℚ := (765906560235234145669745946963427564631115608075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P158 : RatPair2542 := ((-76412795323760950702453897541831405223888820061584721167991663679792731309892781083183713359347 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (-2046643603345236139037093065265428720995497543022944572184380010054250486218073598242202528285657 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P158 : ℚ := (70653610184792832480228265907059215518639085256215 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P158 :
    phaseExp2646 phaseArg2658P158 20 =
      ((phaseValue2658P158.1,
        phaseValue2658P158.2), phaseRadius2658P158) := by
  decide +kernel

theorem phaseCosPin2658P158 :
    |Real.cos (phaseArg2658P158 : ℝ) -
      (phaseValue2658P158.1 : ℝ)| ≤
        (phaseRadius2658P158 : ℝ) := by
  have hsmall : |((phaseArg2658P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P158]
  have h := phaseExp_cos_error2646 phaseArg2658P158 20 hsmall
  rw [phaseChain2658P158] at h
  simpa [phaseValue2658P158] using h

theorem phaseSinPin2658P158 :
    |Real.sin (phaseArg2658P158 : ℝ) -
      (phaseValue2658P158.2 : ℝ)| ≤
        (phaseRadius2658P158 : ℝ) := by
  have hsmall : |((phaseArg2658P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P158]
  have h := phaseExp_sin_error2646 phaseArg2658P158 20 hsmall
  rw [phaseChain2658P158] at h
  simpa [phaseValue2658P158] using h

end ConnesWeilRH.Dev
