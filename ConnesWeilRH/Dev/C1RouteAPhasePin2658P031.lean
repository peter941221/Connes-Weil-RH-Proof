import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 031 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P031 : ℚ := (-765906560235234145669745946963427564631115608075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P031 : RatPair2542 := ((-611302362590087605619631180334651241791110560492677769343933309438341850479142248665469704869105 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (2046643603345236139037093065265428720995497543022944572184380010054250486218073598242202528906353 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P031 : ℚ := (70653610184792832480228265907059215518639085256215 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P031 :
    phaseExp2646 phaseArg2658P031 20 =
      ((phaseValue2658P031.1,
        phaseValue2658P031.2), phaseRadius2658P031) := by
  decide +kernel

theorem phaseCosPin2658P031 :
    |Real.cos (phaseArg2658P031 : ℝ) -
      (phaseValue2658P031.1 : ℝ)| ≤
        (phaseRadius2658P031 : ℝ) := by
  have hsmall : |((phaseArg2658P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P031]
  have h := phaseExp_cos_error2646 phaseArg2658P031 20 hsmall
  rw [phaseChain2658P031] at h
  simpa [phaseValue2658P031] using h

theorem phaseSinPin2658P031 :
    |Real.sin (phaseArg2658P031 : ℝ) -
      (phaseValue2658P031.2 : ℝ)| ≤
        (phaseRadius2658P031 : ℝ) := by
  have hsmall : |((phaseArg2658P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P031]
  have h := phaseExp_sin_error2646 phaseArg2658P031 20 hsmall
  rw [phaseChain2658P031] at h
  simpa [phaseValue2658P031] using h

end ConnesWeilRH.Dev
